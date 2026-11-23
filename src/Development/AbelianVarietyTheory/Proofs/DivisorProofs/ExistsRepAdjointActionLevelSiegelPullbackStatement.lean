module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointActionsOrderFiniteUnramifiedSchemeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningPosDefRelationHarrisTaylorOrderStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRepresentingLinearLevelsAbelianSchem
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRepRosatiOrderActionsSiegel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.UPel.HT

open GlobalTheory.EndLoc

variable {p : ℕ} [Fact p.Prime] {S : Scheme.{0}}

def opBar (D : Datum p) (a : D.Oᵐᵒᵖ) : D.Oᵐᵒᵖ := MulOpposite.op ((D.star a.unop).unop)

theorem opBar_add (D : Datum p) (a b : D.Oᵐᵒᵖ) : opBar D (a + b) = opBar D a + opBar D b := by
  simp [opBar]

theorem isRAct_of_oActN (D : Datum p) {A : Over S} [GrpObj A] (act : OActN D.O A) :
    IsRAct A (fun a : D.Oᵐᵒᵖ => act.act a.unop) :=
  ⟨fun _ => act.hom _, act.one, fun a b => act.mul b.unop a.unop, fun a b => act.add _ _⟩

theorem adj_of_rosatiFor (D : Datum p) {A : Over S} [GrpObj A] (act : OActN D.O A) (P : LB (G2 A).left)
    (h : RosatiFor D act P) : Adj A P (opBar D) (fun a : D.Oᵐᵒᵖ => act.act a.unop) :=
  fun a => h a.unop

def oActNOfIsRAct (D : Datum p) {A : Over S} [GrpObj A] {act : D.Oᵐᵒᵖ → (A ⟶ A)} (h : IsRAct A act) :
    OActN D.O A where
  act c := act (MulOpposite.op c)
  hom c := h.1 _
  one := h.2.1
  mul b c := h.2.2.1 (MulOpposite.op c) (MulOpposite.op b)
  add b c := h.2.2.2 _ _

theorem rosatiFor_of_adj (D : Datum p) {A : Over S} [GrpObj A] {act : D.Oᵐᵒᵖ → (A ⟶ A)} (h : IsRAct A act)
    (P : LB (G2 A).left) (ha : Adj A P (opBar D) act) : RosatiFor D (oActNOfIsRAct D h) P :=
  fun c => ha (MulOpposite.op c)

theorem exists_finite_rep_oActN_rosati : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (c : SiegPre h M ζ s₁), Out.RelAmple c.A c.diag → ∃ (H : Scheme.{0}) (πH : H ⟶ S) (AH : Over H) (_ : GrpObj AH) (_ : IsCommMonObj AH) (φH : AH.left ⟶ c.A.left) (φ₂H : (G2 AH).left ⟶ (G2 c.A).left) (actH : OActN D.O AH), IsFinite πH ∧ IsAbelianScheme AH ∧ IsGrpPullback AH c.A πH φH ∧ IsSquare φH φ₂H ∧ RosatiFor D actH (c.P.pull φ₂H) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ c.A.left) (φ₂ : (G2 AT).left ⟶ (G2 c.A).left) (act : OActN D.O AT), IsGrpPullback AT c.A g φ → IsSquare φ φ₂ → RosatiFor D act (c.P.pull φ₂) → ∃! z : T ⟶ H, z ≫ πH = g ∧ ∃ ψ : AT.left ⟶ AH.left, IsGrpPullback AT AH z ψ ∧ ψ ≫ φH = φ ∧ ∀ a : D.O, (act.act a).left ≫ ψ = ψ ≫ (actH.act a).left := by
  intro p _ D h M B _ ζ S _ s₁ c hample
  obtain ⟨r, e, W, d, hspan, hpos, hd, hsum⟩ := GlobalTheory.T.exists_spanning_posDef_relation_harrisTaylorOrder p D
  obtain ⟨R, hfin, -⟩ := GlobalTheory.T.adjointActions_order_finite_unramified_scheme S c.A c.P c.ab c.isLB c.rig₁ c.rig₂ c.symm hample D.Oᵐᵒᵖ (opBar D) r e W d
    (opBar_add D) hspan hpos hd hsum
  have hcomm : IsCommMonObj R.AH := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback R.pb
  refine ⟨R.H, R.π, R.AH, R.grp, hcomm, R.φ, R.φ₂, oActNOfIsRAct D R.isAct, hfin,
    GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab R.pb, R.pb, R.sq, rosatiFor_of_adj D R.isAct _ R.adj, ?_⟩
  intro T g AT _ φ φ₂ act hpb hsq hros
  obtain ⟨z, ⟨hz, ψ, hψ, hψφ, hψa⟩, huniq⟩ :=
    R.rep T g AT φ φ₂ _ hpb hsq (isRAct_of_oActN D act) (adj_of_rosatiFor D act _ hros)
  refine ⟨z, ⟨hz, ψ, hψ, hψφ, fun a => hψa (MulOpposite.op a)⟩, ?_⟩
  rintro z' ⟨hz', ψ', hψ', hψφ', hψa'⟩
  exact huniq z' ⟨hz', ψ', hψ', hψφ', fun a => hψa' a.unop⟩

end GlobalTheory.UPel.HT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRepRosatiOrderActionsSiegelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.exists_finite_rep_rosati_orderActions_siegel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (c : SiegPre h M ζ s₁), Out.RelAmple c.A c.diag → ∃ (H : Scheme.{0}) (πH : H ⟶ S) (AH : Over H) (_ : GrpObj AH) (_ : IsCommMonObj AH) (φH : AH.left ⟶ c.A.left) (φ₂H : (G2 AH).left ⟶ (G2 c.A).left) (actH : OActN D.O AH), IsFinite πH ∧ IsAbelianScheme AH ∧ IsGrpPullback AH c.A πH φH ∧ IsSquare φH φ₂H ∧ RosatiFor D actH (c.P.pull φ₂H) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ c.A.left) (φ₂ : (G2 AT).left ⟶ (G2 c.A).left) (act : OActN D.O AT), IsGrpPullback AT c.A g φ → IsSquare φ φ₂ → RosatiFor D act (c.P.pull φ₂) → ∃! z : T ⟶ H, z ≫ πH = g ∧ ∃ ψ : AT.left ⟶ AH.left, IsGrpPullback AT AH z ψ ∧ ψ ≫ φH = φ ∧ ∀ a : D.O, (act.act a).left ≫ ψ = ψ ≫ (actH.act a).left := by
  first | (exact @GlobalTheory.UPel.HT.exists_finite_rep_oActN_rosati) | (exact GlobalTheory.UPel.HT.exists_finite_rep_oActN_rosati) | (intros; apply GlobalTheory.UPel.HT.exists_finite_rep_oActN_rosati  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRepresentingLinearLevelsAbelianSchemStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.exists_finite_representing_linearLevels_abelianScheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] [IsCommMonObj AH], IsAbelianScheme AH → IsUnit ((N : ℕ) : Γ(H, ⊤)) → ∀ (actH : OActN D.O AH), ∃ (E : Scheme.{0}) (πE : E ⟶ H) (AE : Over E) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ AH.left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over E) ⟶ AE)), IsFinite πE ∧ IsGrpPullback AE AH πE φE ∧ (∀ a : D.O, (actE.act a).left ≫ φE = φE ≫ (actH.act a).left) ∧ EtaOK D N actE ηE ∧ ∀ (T : Scheme.{0}) (g : T ⟶ H) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ AH.left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT AH g φ → (∀ a : D.O, (act.act a).left ≫ φ = φ ≫ (actH.act a).left) → EtaOK D N act eta → ∃! z : T ⟶ E, z ≫ πE = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  first | (exact @GlobalTheory.UPel.HT.exists_finite_rep_linLevel) | (exact GlobalTheory.UPel.HT.exists_finite_rep_linLevel) | (intros; apply GlobalTheory.UPel.HT.exists_finite_rep_linLevel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionOfGrpPullbackSquare

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.RosatiPull

theorem sq_left_ext {H : Scheme.{0}} {G : Over H} {Z : Scheme.{0}} {a b : Z ⟶ (G ⊗ G).left}
    (h1 : a ≫ (fst G G).left = b ≫ (fst G G).left) (h2 : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b :=
  pullback.hom_ext h1 h2

theorem rosatiFor_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (S H E : Scheme.{0}) (A₀ : Over S) [GrpObj A₀] (P : LB (G2 A₀).left), P.IsLB → ∀ (AH : Over H) [GrpObj AH] (AE : Over E) [GrpObj AE] (f : E ⟶ H) (φ : AE.left ⟶ AH.left) (φ₂ : (G2 AE).left ⟶ (G2 AH).left) (φ₂H : (G2 AH).left ⟶ (G2 A₀).left) (actH : OActN D.O AH) (actE : OActN D.O AE), IsGrpPullback AE AH f φ → IsSquare φ φ₂ → (∀ a : D.O, (actE.act a).left ≫ φ = φ ≫ (actH.act a).left) → RosatiFor D actH (P.pull φ₂H) → RosatiFor D actE (P.pull (φ₂ ≫ φ₂H)) := by
  intro p _ D S H E A₀ _ P hP AH _ AE _ f φ φ₂ φ₂H actH actE _ hsq hact hR c
  have hu : (lift (fst AE AE ≫ actE.act c) (snd AE AE)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst AH AH ≫ actH.act c) (snd AH AH)).left := by
    apply sq_left_ext
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hsq.1]
      simp only [← Category.assoc, ← Over.comp_left, lift_fst]
      simp only [Over.comp_left, Category.assoc, hact]
      rw [← Category.assoc φ₂, hsq.1, Category.assoc]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hsq.2]
      simp only [← Category.assoc, ← Over.comp_left, lift_snd]
  have hv : (lift (fst AE AE) (snd AE AE ≫ actE.act (D.star c).unop)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst AH AH) (snd AH AH ≫ actH.act (D.star c).unop)).left := by
    apply sq_left_ext
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hsq.1]
      simp only [← Category.assoc, ← Over.comp_left, lift_fst]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hsq.2]
      simp only [← Category.assoc, ← Over.comp_left, lift_snd]
      simp only [Over.comp_left, Category.assoc, hact]
      rw [← Category.assoc φ₂, hsq.2, Category.assoc]
  have hQ : (P.pull φ₂H).IsLB := pull_isLB hP _
  have hR' : (P.pull (φ₂ ≫ φ₂H)).IsLB := pull_isLB hP _
  have e3 := GlobalTheory.GenSpread.lbIso_pull_comp (L := P.pull φ₂H) (M := P.pull φ₂H) φ₂ hu hv (hR c)
  have e1u := GlobalTheory.GenSpread.lbIso_pull_pull hP
    (lift (fst AE AE ≫ actE.act c) (snd AE AE)).left (a := φ₂ ≫ φ₂H) rfl
  have e2u := GlobalTheory.GenSpread.lbIso_pull_pull hP
    ((lift (fst AE AE ≫ actE.act c) (snd AE AE)).left ≫ φ₂) (a := φ₂H) (Category.assoc _ _ _).symm
  have e1v := GlobalTheory.GenSpread.lbIso_pull_pull hP
    (lift (fst AE AE) (snd AE AE ≫ actE.act (D.star c).unop)).left (a := φ₂ ≫ φ₂H) rfl
  have e2v := GlobalTheory.GenSpread.lbIso_pull_pull hP
    ((lift (fst AE AE) (snd AE AE ≫ actE.act (D.star c).unop)).left ≫ φ₂) (a := φ₂H) (Category.assoc _ _ _).symm
  exact LBIso.trans (pull_isLB hR' _) (pull_isLB hP _) (pull_isLB hR' _) e1u.symm
    (LBIso.trans (pull_isLB hP _) (pull_isLB hQ _) (pull_isLB hR' _) e2u
      (LBIso.trans (pull_isLB hQ _) (pull_isLB hQ _) (pull_isLB hR' _) e3
        (LBIso.trans (pull_isLB hQ _) (pull_isLB hP _) (pull_isLB hR' _) e2v.symm e1v)))

end GlobalTheory.RosatiPull
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionOfGrpPullbackSquareStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.rosatiCondition_of_grpPullback_square : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (S H E : Scheme.{0}) (A₀ : Over S) [GrpObj A₀] (P : LB (G2 A₀).left), P.IsLB → ∀ (AH : Over H) [GrpObj AH] (AE : Over E) [GrpObj AE] (f : E ⟶ H) (φ : AE.left ⟶ AH.left) (φ₂ : (G2 AE).left ⟶ (G2 AH).left) (φ₂H : (G2 AH).left ⟶ (G2 A₀).left) (actH : OActN D.O AH) (actE : OActN D.O AE), IsGrpPullback AE AH f φ → IsSquare φ φ₂ → (∀ a : D.O, (actE.act a).left ≫ φ = φ ≫ (actH.act a).left) → RosatiFor D actH (P.pull φ₂H) → RosatiFor D actE (P.pull (φ₂ ≫ φ₂H)) := by
  first | (exact @GlobalTheory.RosatiPull.rosatiFor_pull) | (exact GlobalTheory.RosatiPull.rosatiFor_pull) | (intros; apply GlobalTheory.RosatiPull.rosatiFor_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepAdjointActionLevelSiegelPullback

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem exists_finite_rep_rosati_level : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∃ (E : Scheme.{0}) (πE : E ⟶ S) (AE : Over E) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ c.A.left) (φ₂E : (G2 AE).left ⟶ (G2 c.A).left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over E) ⟶ AE)), IsLocallyNoetherian E ∧ IsFinite πE ∧ IsGrpPullback AE c.A πE φE ∧ IsSquare φE φ₂E ∧ RosatiFor D actE (c.P.pull φ₂E) ∧ EtaOK D N actE ηE ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ c.A.left) (φ₂ : (G2 AT).left ⟶ (G2 c.A).left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT c.A g φ → IsSquare φ φ₂ → RosatiFor D act (c.P.pull φ₂) → EtaOK D N act eta → ∃! z : T ⟶ E, z ≫ πE = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ (∀ a : D.O, (act.act a).left ≫ ψ = ψ ≫ (actE.act a).left) ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  intro p _ D R _ b N hNp h M B _ ζ S _ s₁ t c e he hc
  obtain ⟨H, πH, AH, _, _, φH, φ₂H, actH, hHf, hHab, pbH, sqH, rosH, univH⟩ := GlobalTheory.T.exists_finite_rep_rosati_orderActions_siegel p D h M B ζ S s₁ c hc.1
  have hNH : IsUnit ((N : ℕ) : Γ(H, ⊤)) := by
    have h0 : IsUnit ((N : ℕ) : Γ(Sp R, ⊤)) := by
      have := (b.unit N hNp).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      simpa using this
    have := h0.map (πH ≫ t).appTop.hom
    simpa using this
  obtain ⟨E, πE, AE, _, _, φE, actE, ηE, hEf, pbE, actEc, etaE, univE⟩ := GlobalTheory.T.exists_finite_representing_linearLevels_abelianScheme p D N H AH hHab hNH actH
  let x₁ : Over.mk ((G2 AE).hom ≫ πE) ⟶ AH :=
    Over.homMk ((fst AE AE).left ≫ φE) (by rw [Category.assoc, pbE.1.w, ← Category.assoc, Over.w]; rfl)
  let x₂ : Over.mk ((G2 AE).hom ≫ πE) ⟶ AH :=
    Over.homMk ((snd AE AE).left ≫ φE) (by rw [Category.assoc, pbE.1.w, ← Category.assoc, Over.w]; rfl)
  let φ₂ : (G2 AE).left ⟶ (G2 AH).left := (lift x₁ x₂).left
  have sq : IsSquare φE φ₂ := by
    constructor
    · show (lift x₁ x₂).left ≫ (fst AH AH).left = _
      rw [← Over.comp_left, lift_fst]; rfl
    · show (lift x₁ x₂).left ≫ (snd AH AH).left = _
      rw [← Over.comp_left, lift_snd]; rfl
  haveI : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian πH
  haveI : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian πE
  refine ⟨E, πE ≫ πH, AE, inferInstance, inferInstance, φE ≫ φH, φ₂ ≫ φ₂H, actE, ηE, inferInstance,
    inferInstance, pbE.comp pbH, ?_, GlobalTheory.T.rosatiCondition_of_grpPullback_square p D S H E c.A c.P c.isLB AH AE πE φE φ₂ φ₂H actH actE pbE sq actEc rosH,
    etaE, ?_⟩
  · constructor
    · rw [Category.assoc, sqH.1, ← Category.assoc, sq.1, Category.assoc]
    · rw [Category.assoc, sqH.2, ← Category.assoc, sq.2, Category.assoc]
  intro T g AT _ φ φ₂' act eta pbT sqT rosT etaT
  obtain ⟨z₁, ⟨hz₁, ψ₁, pb₁, hψ₁, act₁⟩, uniq₁⟩ := univH T g AT φ φ₂' act pbT sqT rosT
  obtain ⟨z, ⟨hz, ψ, pb, hψ, heta⟩, uniq⟩ := univE T z₁ AT ψ₁ act eta pb₁ act₁ etaT
  refine ⟨z, ⟨by rw [← Category.assoc, hz, hz₁], ψ, pb, by rw [← Category.assoc, hψ, hψ₁], fun a => ?_, heta⟩, ?_⟩
  · apply pbE.1.hom_ext
    · rw [Category.assoc, hψ, act₁, Category.assoc, actEc, ← Category.assoc, hψ]
    · rw [Category.assoc, pb.1.w, Category.assoc, Over.w (actE.act a), pb.1.w, ← Category.assoc, Over.w (act.act a)]
  · rintro z' ⟨hz', ψ', pb', hψ', act', eta'⟩
    have e₁ : z' ≫ πE = z₁ := uniq₁ (z' ≫ πE) ⟨by rw [Category.assoc]; exact hz', ψ' ≫ φE, pb'.comp pbE,
      by rw [Category.assoc]; exact hψ', fun a => by
        rw [← Category.assoc, act' a, Category.assoc, actEc, Category.assoc]⟩
    have e₂ : ψ' ≫ φE = ψ₁ := by
      apply pbH.1.hom_ext
      · rw [Category.assoc, hψ', hψ₁]
      · rw [Category.assoc, pbE.1.w, ← Category.assoc, pb'.1.w, Category.assoc, e₁, pb₁.1.w]
    exact uniq z' ⟨e₁, ψ', pb', e₂, eta'⟩

end GlobalTheory.UPel.HT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepAdjointActionLevelSiegelPullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.exists_rep_adjointAction_level_siegelPullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∃ (E : Scheme.{0}) (πE : E ⟶ S) (AE : Over E) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ c.A.left) (φ₂E : (G2 AE).left ⟶ (G2 c.A).left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over E) ⟶ AE)), IsLocallyNoetherian E ∧ IsFinite πE ∧ IsGrpPullback AE c.A πE φE ∧ IsSquare φE φ₂E ∧ RosatiFor D actE (c.P.pull φ₂E) ∧ EtaOK D N actE ηE ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ c.A.left) (φ₂ : (G2 AT).left ⟶ (G2 c.A).left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT c.A g φ → IsSquare φ φ₂ → RosatiFor D act (c.P.pull φ₂) → EtaOK D N act eta → ∃! z : T ⟶ E, z ≫ πE = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ (∀ a : D.O, (act.act a).left ≫ ψ = ψ ≫ (actE.act a).left) ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  first | (exact @GlobalTheory.UPel.HT.exists_finite_rep_rosati_level) | (exact GlobalTheory.UPel.HT.exists_finite_rep_rosati_level) | (intros; apply GlobalTheory.UPel.HT.exists_finite_rep_rosati_level  <;> assumption)
end
end
