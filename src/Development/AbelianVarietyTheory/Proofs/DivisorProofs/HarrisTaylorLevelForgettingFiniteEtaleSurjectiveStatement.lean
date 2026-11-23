module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleLevelLiftScheme
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePointOfLevelLiftHarrisTaylorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudePrimeToPPullbackSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudeIffOfSpecializesGeometricPointsStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleLevelLiftSchemeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_finite_etale_level_lift_scheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ), N'.Coprime p → N ∣ N' → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Over S) (ηu : D.La → (Y ⟶ o.A)), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (T : Over S) (lv : D.La → (T ⟶ o.A)), (IsLift o N' T lv → ∃! f : T ⟶ Y, ∀ a, f ≫ ηu a = lv a) ∧ ((∃ f : T ⟶ Y, ∀ a, f ≫ ηu a = lv a) → IsLift o N' T lv) := by
  first | exact @GlobalTheory.UPel.HT.exists_liftScheme | exact GlobalTheory.UPel.HT.exists_liftScheme | (intros; apply GlobalTheory.UPel.HT.exists_liftScheme <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorHigherLevelPointsEqOfSameImage

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.UPel.HT.MapComp

namespace GlobalTheory.UPel.HT.LiftUniq

theorem eq_of_same_image : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (M' : Model b N') (π : M'.X ⟶ S), π ≫ s = M'.s → ∀ (om : ObjMap (M'.univ.forget N hd hc) o π) (T : Scheme.{0}) (g₁ g₂ : T ⟶ M'.X), g₁ ≫ π = g₂ ≫ π → (∀ a, g₁ ≫ (M'.univ.eta a).left ≫ om.φ = g₂ ≫ (M'.univ.eta a).left ≫ om.φ) → g₁ = g₂ := by
  intro p _ D R _ b N N' hd hc S s o M' π hπ om T g₁ g₂ hg hη
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N' M'.X T M'.s g₁ M'.univ
  obtain ⟨ψ, ψ₂, hcart, hsq, hact0, hpol, hη'⟩ : ∃ (ψ : M'.univ.A.left ⟶ o.A.left)
      (ψ₂ : (M'.univ.A ⊗ M'.univ.A).left ⟶ (o.A ⊗ o.A).left), IsGrpPullback M'.univ.A o.A π ψ ∧
      IsSquare ψ ψ₂ ∧ (∀ c, (M'.univ.act.act c).left ≫ ψ = ψ ≫ (o.act.act c).left) ∧
      Nonempty (LBIso M'.univ.P (o.P.pull ψ₂)) ∧
      (∀ a, g₁ ≫ (M'.univ.eta a).left ≫ ψ = g₂ ≫ (M'.univ.eta a).left ≫ ψ) :=
    ⟨om.φ, om.φ₂, om.cart, om.sq, om.act, ⟨om.pol⟩, hη⟩
  obtain ⟨hpol⟩ := hpol
  clear hη
  have hpb : IsPullback ψ M'.univ.A.hom o.A.hom π := hcart.1
  have w : (m₁.φ ≫ ψ) ≫ o.A.hom = (o₁.A.hom ≫ g₂) ≫ π := by
    have h2 : m₁.φ ≫ M'.univ.A.hom = o₁.A.hom ≫ g₁ := m₁.cart.1.w
    rw [Category.assoc, hpb.w, ← Category.assoc, h2, Category.assoc, hg, Category.assoc]
  obtain ⟨φ, hφ, hφ'⟩ : ∃ φ : o₁.A.left ⟶ M'.univ.A.left, φ ≫ ψ = m₁.φ ≫ ψ ∧
      φ ≫ M'.univ.A.hom = o₁.A.hom ≫ g₂ :=
    ⟨hpb.lift _ _ w, hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
  have n : IsGrpPullback o₁.A o.A (g₂ ≫ π) (φ ≫ ψ) := by
    rw [hφ, ← hg]; exact m₁.cart.comp hcart
  obtain ⟨φ₂, sq⟩ := exists_isSquare hφ'
  have e : m₁.φ₂ ≫ ψ₂ = φ₂ ≫ ψ₂ :=
    isSquare_unique (isSquare_comp m₁.sq hsq) (hφ ▸ isSquare_comp sq hsq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (M'.univ.act.act c).left := by
    intro c
    apply hpb.hom_ext
    · rw [Category.assoc, hφ, ← Category.assoc, m₁.act, Category.assoc, hact0, Category.assoc, hact0,
        ← Category.assoc, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = g₂ ≫ (M'.univ.eta y).left := by
    intro y
    apply hpb.hom_ext
    · rw [Category.assoc, hφ, ← Category.assoc, m₁.eta, Category.assoc, Category.assoc]
      exact hη' y
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ g₂ = g₂ ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  have pol : LBIso o₁.P (M'.univ.P.pull φ₂) :=
    LBIso.trans o₁.isLB (pull_isLB o.isLB _) (pull_isLB M'.univ.isLB _)
      (LBIso.trans o₁.isLB (pull_isLB M'.univ.isLB _) (pull_isLB o.isLB _) m₁.pol
        (lbIso_pull_comp hpol m₁.φ₂ rfl))
      (LBIso.symm (lbIso_pull_comp hpol φ₂ e))
  let m₂ : ObjMap o₁ M'.univ g₂ :=
    { φ := φ, φ₂ := φ₂, cart := hcart.cancel n hφ', sq := sq, act := hact, pol := pol, eta := heta }
  have h2 : g₂ ≫ M'.s = g₁ ≫ M'.s := by rw [← hπ, ← Category.assoc, ← hg, Category.assoc]
  exact ((M'.rep T (g₁ ≫ M'.s) o₁).unique ⟨rfl, ⟨m₁⟩⟩ ⟨h2, ⟨m₂⟩⟩)

end GlobalTheory.UPel.HT.LiftUniq
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorHigherLevelPointsEqOfSameImageStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.harrisTaylor_higherLevel_points_eq_of_same_image : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (M' : Model b N') (π : M'.X ⟶ S), π ≫ s = M'.s → ∀ (om : ObjMap (M'.univ.forget N hd hc) o π) (T : Scheme.{0}) (g₁ g₂ : T ⟶ M'.X), g₁ ≫ π = g₂ ≫ π → (∀ a, g₁ ≫ (M'.univ.eta a).left ≫ om.φ = g₂ ≫ (M'.univ.eta a).left ≫ om.φ) → g₁ = g₂ := by
  first | exact @GlobalTheory.UPel.HT.LiftUniq.eq_of_same_image | exact GlobalTheory.UPel.HT.LiftUniq.eq_of_same_image | (intros; apply GlobalTheory.UPel.HT.LiftUniq.eq_of_same_image <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudePrimeToPPullbackSquareStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.tateSimilitude_prime_to_p_pullback_square : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N' s') (f : S' ⟶ S) (φ : o'.A.left ⟶ o.A.left) (φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left), IsGrpPullback o'.A o.A f φ → IsSquare φ φ₂ → (∀ c, (o'.act.act c).left ≫ φ = φ ≫ (o.act.act c).left) → LBIso o'.P (o.P.pull φ₂) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S'), (∀ I' : TateIsoO D k (Over.mk x ⟶ o'.A) (fun c g => g ≫ o'.act.act c) (fun n g g' z => Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n g g' (unitOn z)), ∃ I : TateIsoO D k (Over.mk (x ≫ f) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ n y, (I.ev n y).left = (I'.ev n y).left ≫ φ) ∧ (∀ I : TateIsoO D k (Over.mk (x ≫ f) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∃ I' : TateIsoO D k (Over.mk x ⟶ o'.A) (fun c g => g ≫ o'.act.act c) (fun n g g' z => Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n g g' (unitOn z)), ∀ n y, (I.ev n y).left = (I'.ev n y).left ≫ φ) := by
  first | exact @GlobalTheory.UPel.HT.tateIsoO_pullback | exact GlobalTheory.UPel.HT.tateIsoO_pullback | (intros; apply GlobalTheory.UPel.HT.tateIsoO_pullback <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIsLevelLiftOfPoint

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem isLift_of_point : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N' s') (f : S' ⟶ S) (om : ObjMap (o'.forget N hd hc) o f) (T : Over S) (g : T.left ⟶ S') (lv : D.La → (T ⟶ o.A)), g ≫ f = T.hom → (∀ a, (lv a).left = g ≫ (o'.eta a).left ≫ om.φ) → IsLift o N' T lv := by
  intro p _ D R _ b N N' hd hc S S' s s' o o' f om T g lv hT hlv
  obtain ⟨T, ⟨⟨⟩⟩, h⟩ := T
  change T ⟶ S' at g
  replace hT : (g ≫ f : T ⟶ S) = h := hT
  subst hT
  obtain ⟨φ, hφ⟩ : ∃ φ : o'.A.left ⟶ o.A.left, φ = om.φ := ⟨om.φ, rfl⟩
  have hlv' : ∀ a, (lv a).left = g ≫ (o'.eta a).left ≫ φ := fun a => by rw [hφ]; exact hlv a
  have cart : IsGrpPullback o'.A o.A f φ := by rw [hφ]; exact om.cart
  have sq : IsSquare φ om.φ₂ := by rw [hφ]; exact om.sq
  have ha : ∀ c, (o'.act.act c).left ≫ φ = φ ≫ (o.act.act c).left := fun c => by rw [hφ]; exact om.act c
  have he : ∀ x, (o'.eta ((N' / N) • x)).left ≫ φ = f ≫ (o.eta x).left := fun x => by rw [hφ]; exact om.eta x
  let T' : Over S' := Over.mk g
  let q : D.La → (T' ⟶ o'.A) := fun a => toUnit T' ≫ o'.eta a
  have hq : ∀ a, (q a).left = g ≫ (o'.eta a).left := fun a => by
    simp only [q, Over.comp_left, Over.toUnit_left]
    rfl
  have key : ∀ a, (lv a).left = (q a).left ≫ φ := fun a => by rw [hlv', hq, Category.assoc]
  have mulx : ∀ x y : D.La, (lv x * lv y).left = (q x * q y).left ≫ φ := fun x y =>
    cart.2 T' (q x) (q y) (lv x) (lv y) (key x) (key y)
  refine ⟨fun x y => ?_, fun x => ?_, fun c x => ?_, fun x => ?_, fun k _ _ x => ?_⟩
  · apply Over.OverMorphism.ext
    rw [mulx, key]
    congr 1
    show (toUnit T' ≫ o'.eta (x + y)).left = (toUnit T' ≫ o'.eta x * toUnit T' ≫ o'.eta y).left
    rw [o'.eta_add, MonObj.comp_mul]
  · have h1 : q (N' • x) = 1 := by
      show toUnit T' ≫ o'.eta (N' • x) = 1
      rw [o'.eta_ker, MonObj.comp_one]
    have hzz : lv (N' • x) * lv (N' • x) = lv (N' • x) * 1 := by
      rw [_root_.mul_one]
      apply Over.OverMorphism.ext
      rw [mulx, key, h1, _root_.mul_one]
    exact mul_left_cancel hzz
  · apply Over.OverMorphism.ext
    rw [Over.comp_left, hlv', hlv', o'.eta_lin, Over.comp_left]
    simp only [Category.assoc, ha]
  · apply Over.OverMorphism.ext
    rw [hlv', he, Over.comp_left, Over.toUnit_left]
    exact (Category.assoc _ _ _).symm
  · obtain ⟨I', hI'⟩ := o'.geom k (x ≫ g) (Spec.preimage ((x ≫ g) ≫ s')).hom (Spec.map_preimage _).symm
    have h3 := (GlobalTheory.T.tateSimilitude_prime_to_p_pullback_square p D R b N N' S S' s s' o o' f φ om.φ₂ cart sq ha om.pol k (x ≫ g)).1 I'
    rw [Category.assoc] at h3
    obtain ⟨I, hI⟩ := h3
    refine ⟨I, fun y => ?_⟩
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hI, ← hI' y, Over.comp_left, Over.toUnit_left]
    change x ≫ (lv y).left = _
    rw [hlv']
    simp only [Over.mk_hom, Category.assoc]

end GlobalTheory.UPel.HT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIsLevelLiftOfPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.harrisTaylor_isLevelLift_of_point : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N' s') (f : S' ⟶ S) (om : ObjMap (o'.forget N hd hc) o f) (T : Over S) (g : T.left ⟶ S') (lv : D.La → (T ⟶ o.A)), g ≫ f = T.hom → (∀ a, (lv a).left = g ≫ (o'.eta a).left ≫ om.φ) → IsLift o N' T lv := by
  first | exact @GlobalTheory.UPel.HT.isLift_of_point | exact GlobalTheory.UPel.HT.isLift_of_point | (intros; apply GlobalTheory.UPel.HT.isLift_of_point <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLevelForgettingFiniteEtaleSurjective

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem forget_map_finite_etale_surjective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p), 3 ≤ N → ∀ (M : Model b N) (M' : Model b N') (t : M'.X ⟶ M.X), t ≫ M.s = M'.s → Nonempty (ObjMap (M'.univ.forget N hd hc) M.univ t) → IsFinite t ∧ Etale t ∧ Surjective t := by
  intro p _ D R _ _ b N N' hd hc h3 M M' π hπ ⟨om⟩
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨Y, ηu, hYf, hYe, HY⟩ := GlobalTheory.T.exists_finite_etale_level_lift_scheme p D R b N N' hc hd M.X M.s M.univ
  let T0 : Over M.X := Over.mk π
  have hw : ∀ a, ((M'.univ.eta a).left ≫ om.φ) ≫ M.univ.A.hom = T0.hom := fun a => by
    have w : (om.φ : M'.univ.A.left ⟶ M.univ.A.left) ≫ M.univ.A.hom = M'.univ.A.hom ≫ π := om.cart.1.w
    have w2 : (M'.univ.eta a).left ≫ M'.univ.A.hom = 𝟙 M'.X := Over.w (M'.univ.eta a)
    show ((M'.univ.eta a).left ≫ om.φ) ≫ M.univ.A.hom = π
    erw [Category.assoc, w, ← Category.assoc, w2, Category.id_comp]
  let lv0 : D.La → (T0 ⟶ M.univ.A) := fun a => Over.homMk ((M'.univ.eta a).left ≫ om.φ) (hw a)
  have hl0 : IsLift M.univ N' T0 lv0 :=
    GlobalTheory.T.harrisTaylor_isLevelLift_of_point p D R b N N' hd hc M.X M'.X M.s M'.s M.univ M'.univ π om T0 (𝟙 M'.X) lv0
      (Category.id_comp π) fun a => (Category.id_comp _).symm
  obtain ⟨g0, hg0, -⟩ := (HY T0 lv0).1 hl0
  have hlY : IsLift M.univ N' Y ηu := (HY Y ηu).2 ⟨𝟙 Y, fun a => Category.id_comp _⟩
  obtain ⟨h, hh, hha⟩ := GlobalTheory.T.exists_unique_point_of_level_lift_harrisTaylor p D R b N N' h3 hd hc M M' π hπ om Y ηu hlY
  have e1 : g0.left ≫ h = 𝟙 M'.X := by
    refine GlobalTheory.T.harrisTaylor_higherLevel_points_eq_of_same_image p D R b N N' hd hc M.X M.s M.univ M' π hπ om M'.X _ _ ?_ fun a => ?_
    · rw [Category.assoc, hh, Over.w g0, Category.id_comp]
      rfl
    · rw [Category.id_comp, Category.assoc, ← hha a, ← Over.comp_left, hg0 a]
      rfl
  let hY : Y ⟶ T0 := Over.homMk h hh
  have e2 : hY ≫ g0 = 𝟙 Y := by
    obtain ⟨f, -, hf⟩ := (HY Y ηu).1 hlY
    have a1 := hf (hY ≫ g0) fun a => by
      rw [Category.assoc, hg0 a]
      ext
      simp only [Over.comp_left, Over.homMk_left, hY, lv0]
      rw [hha a]
    have a2 := hf (𝟙 Y) fun a => Category.id_comp _
    rw [a1, a2]
  have e2' : h ≫ g0.left = 𝟙 Y.left := by
    have := congrArg (fun q => q.left) e2
    simpa [hY] using this
  haveI : IsIso g0.left := ⟨⟨h, e1, e2'⟩⟩
  have e : π = g0.left ≫ Y.hom := (Over.w g0).symm
  have hfe : IsFinite π ∧ Etale π := by
    rw [e]
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨hfe.1, hfe.2, ⟨fun z => ?_⟩⟩

  obtain ⟨k, _, _, g, hg⟩ := GlobalTheory.FinEt.exists_algClosed_point M.X z
  obtain ⟨β, hβ⟩ : ∃ β : R →+* k, g ≫ M.s = spMap β :=
    ⟨(Spec.preimage (g ≫ M.s)).hom, by simp [spMap]⟩
  obtain ⟨I, hI⟩ := M.univ.geom k g β hβ
  have hN' : 0 < N' := levelPos_of_coprime hc
  have hN : 0 < N := by omega
  have hk : 0 < N' / N := Nat.div_pos (Nat.le_of_dvd hN' hd) hN
  let T : Over M.X := Over.mk g
  let lv : D.La → (T ⟶ M.univ.A) := fun a => I.ev N' a
  have hadd : ∀ x y, lv (x + y) = lv x * lv y := fun x y => I.add N' x y
  have hker : ∀ x, lv (N' • x) = 1 := fun x => (I.ker N' hN' hc _).2 ⟨x, rfl⟩
  have hlin : ∀ (c : D.O) x, lv (c • x) = lv x ≫ M.univ.act.act c := fun c x => I.lin N' c x
  haveI : IsLocallyNoetherian T.left := by
    show IsLocallyNoetherian (Spec (CommRingCat.of k))
    infer_instance
  have hlv : IsLift M.univ N' T lv := by
    refine ⟨hadd, hker, hlin, fun x => ?_, fun k' _ _ x' => ?_⟩
    · show I.ev N' ((N' / N) • x) = toUnit T ≫ M.univ.eta x
      rw [hI x, I.ev_nsmul]
      have := I.tower N (N' / N) hN hk (by rw [Nat.mul_div_cancel' hd]; exact hc) x
      rwa [Nat.mul_div_cancel' hd] at this
    · have h0 : TateAt M.univ N' g (fun a => lv a) := ⟨I, fun y => rfl⟩
      have h1 : TateAt M.univ N' (𝟙 T.left ≫ T.hom)
          (fun a => (Over.homMk (𝟙 T.left) rfl : Over.mk (𝟙 T.left ≫ T.hom) ⟶ T) ≫ lv a) :=
        tateAt_congr M.univ N' (Category.id_comp g).symm _ _ (fun a => by congr 1) h0
      exact (GlobalTheory.T.tateSimilitude_iff_of_specializes_geometric_points p D R b N N' hc M.X M.s M.univ T lv hadd hker hlin (𝟙 T.left) x'
        (x'.base (⊥ : PrimeSpectrum k')) (⊥ : PrimeSpectrum k') (by
          first
          | exact specializes_rfl
          | (rw [Scheme.id.base_apply])
          | (simp only [Scheme.Hom.id_apply]; exact specializes_rfl)
          | exact (Subsingleton.elim (α := PrimeSpectrum k) _ _) ▸ specializes_rfl)).1 h1
  obtain ⟨f, -, -⟩ := (HY T lv).1 hlv
  obtain ⟨u, hu⟩ : z ∈ Set.range g := by rw [hg]; rfl
  refine ⟨(f.left ≫ h).base u, ?_⟩
  have hf : f.left ≫ h ≫ π = g := by rw [hh]; exact Over.w f
  rw [← hu, ← hf]
  rfl

end GlobalTheory.UPel.HT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLevelForgettingFiniteEtaleSurjectiveStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem _root_.GlobalTheory.T.harrisTaylor_levelForgetting_finite_etale_surjective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p), 3 ≤ N → ∀ (M : Model b N) (M' : Model b N') (t : M'.X ⟶ M.X), t ≫ M.s = M'.s → Nonempty (ObjMap (M'.univ.forget N hd hc) M.univ t) → IsFinite t ∧ Etale t ∧ Surjective t := by
  first | exact @GlobalTheory.UPel.HT.forget_map_finite_etale_surjective | exact GlobalTheory.UPel.HT.forget_map_finite_etale_surjective | (intros; apply GlobalTheory.UPel.HT.forget_map_finite_etale_surjective <;> assumption)
end
end
