module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoTranslateEvenCubicalBundle
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalSymmetricStructureOfGenericSymmetriStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGenericFibreExtendsOverDvrStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricOfLineBundleIsoPullGroupHomStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordOfGenericExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegDataFiniteUnramified
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoTranslateEvenCubicalBundleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_orderTwo_translate_even_cubicalBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → GlobalTheory.Mum.SplitClosed G → GlobalTheory.Mum.TwoTorsRat G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ a : Over.mk (jK R) ⟶ G, a * a = 1 ∧ ∀ P₁ : GlobalTheory.UU.CP G, GlobalTheory.GenTransl.IsGenTransl G P.L.L P₁.L.L a → GlobalTheory.Mum.EvenOn P₁ := by
  first | exact @GlobalTheory.EvenTransl.exists_even_of_transl | exact GlobalTheory.EvenTransl.exists_even_of_transl | (intros; apply GlobalTheory.EvenTransl.exists_even_of_transl <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateCubicalBundlePrincipalPolarisatio

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GenTranslPkg

open GlobalTheory.RigidTranslate GlobalTheory.PolTranslate GlobalTheory.GenTransl

variable {R : Type} [CommRing R] [IsDomain R]

def genPoint (G : Over (Sp R)) (a : Over.mk (jK R) ⟶ G) :
    𝟙_ (Over (Sp (FractionRing R))) ⟶ (Over.pullback (jK R)).obj G :=
  Over.homMk (pullback.lift a.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w a)) (pullback.lift_snd _ _ _)

theorem genPoint_fst (G : Over (Sp R)) (a : Over.mk (jK R) ⟶ G) :
    (genPoint G a).left ≫ pullback.fst G.hom (jK R) = a.left :=
  pullback.lift_fst _ _ _

theorem one_left_fst (G : Over (Sp R)) [GrpObj G] (T : Over (Sp (FractionRing R))) :
    (1 : T ⟶ (Over.pullback (jK R)).obj G).left ≫ pullback.fst G.hom (jK R) =
      (1 : Over.mk (T.hom ≫ jK R) ⟶ G).left := by
  have H := isGrpPullback_pullback G (jK R)
  let c : Over.mk (T.hom ≫ jK R) ⟶ G :=
    Over.homMk ((1 : T ⟶ (Over.pullback (jK R)).obj G).left ≫ pullback.fst G.hom (jK R)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      erw [Over.w (1 : T ⟶ (Over.pullback (jK R)).obj G)]
      rfl)
  have hc : c * c = c := by
    apply Over.OverMorphism.ext
    rw [H.2 T 1 1 c c rfl rfl, _root_.mul_one]
    rfl
  have : c = 1 := mul_eq_left.mp hc
  exact congrArg (fun q => q.left) this

theorem genPoint_mul_self (G : Over (Sp R)) [GrpObj G] (a : Over.mk (jK R) ⟶ G) (ha : a * a = 1) :
    genPoint G a * genPoint G a = 1 := by
  have H := isGrpPullback_pullback G (jK R)
  let T := 𝟙_ (Over (Sp (FractionRing R)))
  let U : Over.mk (T.hom ≫ jK R) ⟶ Over.mk (jK R) := Over.homMk (𝟙 _) (by simp [T])
  have hx : (U ≫ a).left = (genPoint G a).left ≫ pullback.fst G.hom (jK R) := by
    rw [genPoint_fst, Over.comp_left]
    exact Category.id_comp _
  have e := H.2 T (genPoint G a) (genPoint G a) (U ≫ a) (U ≫ a) hx hx
  rw [← MonObj.comp_mul, ha, MonObj.comp_one] at e
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [← e, one_left_fst]
  · erw [Over.w (genPoint G a * genPoint G a), Over.w (1 : T ⟶ (Over.pullback (jK R)).obj G)]

theorem transl_genPoint_fst (G : Over (Sp R)) [GrpObj G] (a : Over.mk (jK R) ⟶ G) :
    (transl (genPoint G a)).left ≫ pullback.fst G.hom (jK R) = (genPr G * genPt G a).left := by
  have H := isGrpPullback_pullback G (jK R)
  refine (H.2 _ (𝟙 _) (toUnit _ ≫ genPoint G a) (genPr G) (genPt G a) ?_ ?_).symm
  · exact (Category.id_comp _).symm
  · show pullback.snd G.hom (jK R) ≫ a.left = _
    rw [Over.comp_left, Category.assoc, genPoint_fst]
    rfl

end GlobalTheory.GenTranslPkg


open GlobalTheory.RigidTranslate GlobalTheory.PolTranslate GlobalTheory.GenTransl GlobalTheory.GenTranslPkg in
theorem GlobalTheory.Mum.exists_transl_pkg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ a : Over.mk (jK R) ⟶ G, a * a = 1 → ∃ (P₁ : GlobalTheory.UU.CP G) (A₁ : PolAV (Sp (FractionRing R))) (gen₁ : (Over.pullback (jK R)).obj G ≅ A₁.A), IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G.hom (jK R))) ∧ LBIso (abelian₂ G P₁.L.L) (abelian₂ G P.L.L) ∧ GlobalTheory.GenTransl.IsGenTransl G P.L.L P₁.L.L a := by
  intro R _ _ _ hR G _ _ hG P A gen hgen hL a ha
  obtain ⟨hdvr, -, -⟩ := hR
  haveI := hdvr
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI : GeometricallyIntegral G.hom := @GlobalTheory.geometricallyIntegral_of_isSemiAbelian _ G _ hG
  haveI := A.isAb.comm
  haveI := A.isAb.proper
  let b := genPoint G a
  have hb : b * b = 1 := genPoint_mul_self G a ha
  let b' : 𝟙_ _ ⟶ A.A := b ≫ gen.hom
  have hb' : b' * b' = 1 := by
    show (b ≫ gen.hom) * (b ≫ gen.hom) = 1
    rw [← MonObj.mul_comp, hb, MonObj.one_comp]
  let L₁ : LB A.A.left := rigTransl A.L b'
  have hL₁ : L₁.IsLB := DVR.linComb_isLB _ A.isLB _ _
  let A₁ : PolAV (Sp (FractionRing R)) :=
    { A := A.A, isAb := A.isAb, g := A.g, smoothDim := A.smoothDim, L := L₁, isLB := hL₁,
      rigid := rigidified_rigTransl A.isLB, sym := sym_rigTransl hb' A.isLB A.sym,
      ample := relAmple_rigTransl hb' A.isLB A.ample, ktriv := kTriv_rigTransl hb' A.isLB A.ktriv }
  let LG := L₁.pull gen.hom.left
  have hLG : LG.IsLB := pull_isLB hL₁ _
  obtain ⟨L', hL', hLL'⟩ := GlobalTheory.T.lineBundle_generic_fibre_extends_over_dvr R G LG hLG
  have hpr : IsProper (pullback.snd G.hom (jK R)) := by
    have e : pullback.snd G.hom (jK R) = gen.hom.left ≫ A.A.hom := (Over.w gen.hom).symm
    have : IsIso gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map gen.hom))
    rw [e]; infer_instance
  have hsym : Out.Sym ((Over.pullback (jK R)).obj G) (L'.pull (pullback.fst G.hom (jK R))) :=
    GlobalTheory.T.symmetric_of_lineBundleIso_pull_groupHom _ _ _ gen.hom hgen L₁ _ hL₁ (pull_isLB hL' _) A₁.sym hLL'
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.T.exists_cubicalSymmetricStructure_of_genericSymmetric R G hG hpr L' hL' hsym
  have hPL := P.L.isLB

  have htr : LBIso LG (P.L.L.pull (genPr G * genPt G a).left) := by
    haveI hU : Unique (Sp (FractionRing R)) := inferInstanceAs (Unique (PrimeSpectrum (FractionRing R)))
    let p0 : (𝟙_ (Over (Sp (FractionRing R)))).left := hU.default
    obtain ⟨i, hi⟩ := exists_chart A.isLB (b'.left p0)
    have h1 : LBIso LG (A.L.pull (gen.hom.left ≫ (transl b').left)) :=
      lbIso_diff_pull A.isLB _ _ _ i fun z => by
        show b'.left ((gen.hom.left ≫ A.A.hom) z) ∈ A.L.U i
        have : (gen.hom.left ≫ A.A.hom) z = p0 := hU.uniq _
        rw [this]
        exact hi
    have e : gen.hom.left ≫ (transl b').left = (transl b).left ≫ gen.hom.left := by
      rw [← Over.comp_left, ← Over.comp_left, comp_transl, transl, MonObj.mul_comp, Category.id_comp,
        Category.assoc]
    rw [e] at h1
    have h2 := GlobalTheory.ZM.SiegClause.lbIso_pull_pull (LBIso.symm hL) (transl b).left
    have h3 := GlobalTheory.ZM.SiegClause.lbIso_pull_pull (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hPL (pullback.fst G.hom (jK R))))
      (transl b).left
    rw [transl_genPoint_fst] at h3
    exact LBIso.trans hLG (pull_isLB A.isLB _) (pull_isLB hPL _) h1
      (LBIso.trans (pull_isLB A.isLB _) (pull_isLB (pull_isLB hPL _) _) (pull_isLB hPL _) (LBIso.symm h2) h3)

  have hext : ExtLam G LG (abelian₂ G P.L.L) := by
    refine ⟨DVR.linComb_isLB _ hPL _ _, fun κ₂ hκ => ?_⟩
    obtain ⟨c, hc⟩ := GlobalTheory.Moduli.cube_of_isLB _ A A.L A.isLB
    have e1 : LBIso (abelian₂ _ LG) ((abelian₂ A.A L₁).pull (gen.hom ⊗ₘ gen.hom).left) :=
      GlobalTheory.ZM.SiegClause.lbIso_lam_pull gen.hom hLG hL₁ (GlobalTheory.PolBaseChange.lbIso_refl hLG)
    have e2 : LBIso (abelian₂ _ (P.L.L.pull (pullback.fst G.hom (jK R))))
        ((abelian₂ A.A A.L).pull (gen.hom ⊗ₘ gen.hom).left) :=
      GlobalTheory.ZM.SiegClause.lbIso_lam_pull gen.hom (pull_isLB hPL _) A.isLB (LBIso.symm hL)
    have e3 := GlobalTheory.ZM.SiegClause.lbIso_pull_pull (lam_rigTransl (t := b') A.isLB c hc) (gen.hom ⊗ₘ gen.hom).left
    rw [Category.comp_id] at e3
    have e4 : LBIso (abelian₂ _ (P.L.L.pull (pullback.fst G.hom (jK R)))) ((abelian₂ G P.L.L).pull κ₂) :=
      GlobalTheory.LamPull.lbIso_lam_pull (isGrpPullback_pullback G (jK R)) hPL (pull_isLB hPL _)
        (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hPL _)) hκ
    have lb : ∀ {S : Scheme.{0}} (H : Over S) [GrpObj H] {M : LB H.left}, M.IsLB → (abelian₂ H M).IsLB :=
      fun _ _ _ h => DVR.linComb_isLB _ h _ _
    exact LBIso.trans (lb _ hLG) (pull_isLB (lb _ hL₁) _) (pull_isLB (lb _ hPL) _) e1
      (LBIso.trans (pull_isLB (lb _ hL₁) _) (pull_isLB (lb _ A.isLB) _) (pull_isLB (lb _ hPL) _) e3
        (LBIso.trans (pull_isLB (lb _ A.isLB) _) (lb _ (pull_isLB hPL _)) (pull_isLB (lb _ hPL) _)
          (LBIso.symm e2) e4))
  refine ⟨P₁, A₁, gen, hgen, ?_, ?_, ?_⟩
  · rw [hP₁]; exact hLL'
  · rw [hP₁]; exact GlobalTheory.T.lineBundleIso_mumford_of_generic_extension R G hG L' LG (abelian₂ G P.L.L) hL' hLG hLL' hext
  · show LBIso _ _
    rw [hP₁]
    exact LBIso.trans (pull_isLB hL' _) hLG (pull_isLB hPL _) (LBIso.symm hLL') htr
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateCubicalBundlePrincipalPolarisatioStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_translateCubicalBundle_principalPolarisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ a : Over.mk (jK R) ⟶ G, a * a = 1 → ∃ (P₁ : GlobalTheory.UU.CP G) (A₁ : PolAV (Sp (FractionRing R))) (gen₁ : (Over.pullback (jK R)).obj G ≅ A₁.A), IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G.hom (jK R))) ∧ LBIso (abelian₂ G P₁.L.L) (abelian₂ G P.L.L) ∧ GlobalTheory.GenTransl.IsGenTransl G P.L.L P₁.L.L a := by
  first | exact @GlobalTheory.Mum.exists_transl_pkg | exact GlobalTheory.Mum.exists_transl_pkg | (intros; apply GlobalTheory.Mum.exists_transl_pkg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenTranslateTwoTorsionSplitClosedFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_even_translate_split : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → SplitClosed G → TwoTorsRat G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (P₁ : GlobalTheory.UU.CP G) (A₁ : PolAV (Sp (FractionRing R))) (gen₁ : (Over.pullback (jK R)).obj G ≅ A₁.A), IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G.hom (jK R))) ∧ LBIso (abelian₂ G P₁.L.L) (abelian₂ G P.L.L) ∧ EvenOn P₁ := by
  intro R _ _ _ hR G _ _ hG hS hT P A gen hgen hL
  obtain ⟨a, ha, hE⟩ := GlobalTheory.T.exists_orderTwo_translate_even_cubicalBundle R hR G hG hS hT P A gen hgen hL
  obtain ⟨P₁, A₁, gen₁, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_translateCubicalBundle_principalPolarisation R hR G hG P A gen hgen hL a ha
  exact ⟨P₁, A₁, gen₁, h1, h2, h3, hE P₁ h4⟩

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenTranslateTwoTorsionSplitClosedFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_even_translate_two_torsion_split_closed_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → SplitClosed G → TwoTorsRat G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (P₁ : GlobalTheory.UU.CP G) (A₁ : PolAV (Sp (FractionRing R))) (gen₁ : (Over.pullback (jK R)).obj G ≅ A₁.A), IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G.hom (jK R))) ∧ LBIso (abelian₂ G P₁.L.L) (abelian₂ G P.L.L) ∧ EvenOn P₁ := by
  first | exact @GlobalTheory.Mum.exists_even_translate_split | exact GlobalTheory.Mum.exists_even_translate_split | (intros; apply GlobalTheory.Mum.exists_even_translate_split <;> assumption)
end
end
