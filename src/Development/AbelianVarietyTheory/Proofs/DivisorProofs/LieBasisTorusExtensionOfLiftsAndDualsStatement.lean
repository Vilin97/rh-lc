module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPointsAddPullTangent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorLiftsToDegenerationPoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTangentCombinationCharacterValuesStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentCharacterValuesAdditive

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.GtTanClass

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem exists_unit {T : Over (Sp R)} (g : GtPt D T) (hb : g.b = 1) (χ : D.X) :
    ∃ ρ : Γ(T.left, ⊤)ˣ, ∀ (Z : Scheme.{0}) (q : Z ⟶ T.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → val (g.s χ) q z J = Geo.Tor.gm q z ⊤ ρ := by
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T g.b χ) (ε' := DegPre.gtε)
    (fun U _ h => Eq.symm (by
      refine (prod_pt g.b χ h).trans ?_
      rw [hb, _root_.mul_one]; simp)) (LB.oneGen D.P.L (Y := T.left))
    (fun i j => (map_one _).trans
      ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  obtain ⟨ρ, hρ⟩ := Geo.Tor.exists_ratio D.P.isLB rfl (g.s χ) u (g.isGen χ) hu
  exact ⟨ρ, fun Z q z J hJ => by rw [hρ Z q z J hJ, vu Z q z J hJ, val_one, _root_.mul_one]⟩

omit [IsDomain R] in
theorem gs_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (z : Sp B) (a : A) :
    gs (spMap f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = toStkA z (f a) := by
  rw [gs_eq _ _ ⊤ trivial]
  have e := congrArg (fun k => k.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact congrArg ((Sp B).presheaf.germ ⊤ z trivial).hom e.symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (gm : GtPt D (epsR R)), GtTan gm → gm.b = DegPre.zeroT D (epsR R) → ∃ l : D.X →+ R, ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (l χ))) := by
  intro R _ _ _ D gm ⟨o, ho, hp⟩ hb
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    simpa only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one] using
      IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  have hb1 : gm.b = 1 := hb
  choose ρ hρ using exists_unit gm hb1
  choose u hu using fun χ =>
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).commRingCatIsoToRingEquiv.symm.surjective (ρ χ).val
  have hv : ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → (val (gm.s χ) q z J).val =
        gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (u χ)) := fun χ Z q z J hJ =>
    (congrArg Units.val (hρ χ Z q z J hJ)).trans ((gs_unit q z ⊤ trivial _).symm.trans
      (congrArg (gs q z ⊤) (hu χ).symm))
  have h1 : ∀ χ, TrivSqZeroExt.fst (u χ : DualNumber R) = 1 := fun χ => by
    obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (cpt R)
    have e : val (gm.s χ) (redE R) (cpt R) J = 1 := by
      have e₁ := (val_corr hJ (hp.2 χ) (𝟙 (Sp R))).trans (val_pull hJ _ _ _)
      have e₂ := (val_corr hJ (ho.2 χ) (𝟙 (Sp R))).trans (val_one _)
      rw [← e₂, e₁]
      congr 1
    have e' := hv χ _ (redE R) (cpt R) J hJ
    rw [e] at e'
    refine toStkA_injective (A := R) ?_
    rw [map_one]
    exact (gs_spMap (TrivSqZeroExt.fstHom R R R).toRingHom (cpt R) (u χ)).symm.trans e'.symm
  have hm : ∀ χ χ', (u (χ + χ') : DualNumber R) = u χ * u χ' := fun χ χ' => by
    obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (cpt (DualNumber R))
    have C : IsCub (th D (T := epsR R) (cpt (DualNumber R)) J) := isCub_cubV D.cub hJ
    have e := cv_add gm hJ χ χ'
    rw [hb1, C.face₃, _root_.mul_one] at e
    have k : ∀ χ, (cv gm χ (cpt (DualNumber R)) J).val = toStkA (cpt (DualNumber R)) (u χ) := fun χ =>
      (hv χ _ (𝟙 _) _ J hJ).trans (gs_eq _ _ ⊤ trivial _)
    refine toStkA_injective (A := DualNumber R) ?_
    rw [map_mul]
    exact (k _).symm.trans ((congrArg Units.val e).trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) (k _) (k _))))
  refine ⟨AddMonoidHom.mk' (fun χ => TrivSqZeroExt.snd (u χ : DualNumber R)) fun χ χ' => ?_, fun χ Z q z J hJ => ?_⟩
  · rw [hm, DualNumber.snd_mul, h1, h1]; ring
  · refine (hv χ Z q z J hJ).trans (congrArg (fun x => gs q z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom x)) ?_)
    exact TrivSqZeroExt.ext (by simp [h1]) (by simp)

end GlobalTheory.MBLow.GtTanClass

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentCharacterValuesAdditiveStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torusExtensionTangent_characterValues_additive : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (gm : GtPt D (epsR R)), GtTan gm → gm.b = DegPre.zeroT D (epsR R) → ∃ l : D.X →+ R, ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (l χ))) := by
  first | exact @GlobalTheory.MBLow.GtTanClass.main | exact GlobalTheory.MBLow.GtTanClass.main | (intros; apply GlobalTheory.MBLow.GtTanClass.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisTorusExtensionOfLiftsAndDuals

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GtBasis

open GlobalTheory.TorusModel

section Tangent

variable {R : Type} [CommRing R]

def redO (R : Type) [CommRing R] : baseOver (Sp R) ⟶ epsR R := Over.homMk (redE R) GlobalTheory.MBLow.GtVec.red_comp

theorem isTangent_iff {G : Over (Sp R)} [GrpObj G] (y : epsR R ⟶ G) : IsTangent y ↔ redO R ≫ y = 1 := by
  constructor
  · intro h
    apply Over.OverMorphism.ext
    refine h.trans ?_
    simp [Hom.one_def]
  · intro h
    have := congrArg (·.left) h
    refine this.trans ?_
    simp [Hom.one_def]

theorem redO_scale (c : R) : redO R ≫ epsScale R c = redO R := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap _ = spMap _
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  simp [epsScaleR]

variable {G : Over (Sp R)} [GrpObj G]

theorem isTangent_mul {y y' : epsR R ⟶ G} (h : IsTangent y) (h' : IsTangent y') : IsTangent (y * y') := by
  rw [isTangent_iff] at *
  rw [MonObj.comp_mul, h, h', _root_.mul_one]

theorem isTangent_inv {y : epsR R ⟶ G} (h : IsTangent y) : IsTangent y⁻¹ := by
  rw [isTangent_iff] at *
  rw [GrpObj.comp_inv, h, inv_one]

theorem isTangent_scale (c : R) {y : epsR R ⟶ G} (h : IsTangent y) : IsTangent (epsScale R c ≫ y) := by
  rw [isTangent_iff] at *
  rw [← Category.assoc, redO_scale, h]

theorem isTangent_tanComb {m : ℕ} (c : Fin m → R) {v : Fin m → (epsR R ⟶ G)} (h : ∀ i, IsTangent (v i)) :
    IsTangent (tanComb c v) := by
  unfold tanComb
  refine List.prod_induction (fun y => IsTangent y) (fun _ _ => isTangent_mul) ?_ ?_
  · exact (isTangent_iff _).2 (MonObj.comp_one _)
  · intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact isTangent_scale _ (h i)

theorem eq_tanComb' {m : ℕ} {c : Fin m → R} {v : Fin m → (epsR R ⟶ G)} {w : epsR R ⟶ G} (h : IsLieComb c v w) :
    w = tanComb c v := by
  obtain ⟨u, hu, rfl⟩ := h
  unfold tanComb
  congr 2
  exact funext fun i => Over.OverMorphism.ext (hu i)

end Tangent

section Stalk

variable {R : Type} [CommRing R]

theorem gs_id_eq (z : Sp R) (a : R) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 (Sp R)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = toStkA z a := by
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_eq _ z ⊤ trivial]
  simp [toStkA]
  rfl

theorem dn_inj [IsLocalRing (DualNumber R)] {a a' : R}
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 (Sp (DualNumber R))) (cpt (DualNumber R)) ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr a)) =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 (Sp (DualNumber R))) (cpt (DualNumber R)) ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr a'))) : a = a' := by
  rw [gs_id_eq, gs_id_eq] at h
  exact TrivSqZeroExt.inr_injective (add_left_cancel (toStkA_injective h))

end Stalk

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (H : Over (Sp R)) [GrpObj H] [IsCommMonObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ → ∀ (r : ℕ) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (bX : Module.Basis (Fin r) ℤ D.X) (x : Fin D.P.g ⊕ Fin r → (epsR R ⟶ H)), IsLieBasis vB → (∀ j, GtTan (Φ _ (x j))) → (∀ i, (Φ _ (x (Sum.inl i))).b = vB i) → (∀ l, (Φ _ (x (Sum.inr l))).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (x (Sum.inr l))).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr ((bX.repr χ l : ℤ) : R)))) → ∀ (n : ℕ) (σ : Fin n ≃ Fin D.P.g ⊕ Fin r), IsLieBasis (fun k => x (σ k)) := by
  intro R _ _ _ D H _ _ Φ hΦ r vB bX x hvB htan hb htor n σ
  have hz : ∀ T, (Φ T 1).IsZero := fun T => GtVec.isZero_of_isAdd (by simpa using hΦ.2 T 1 1)
  have bpull : ∀ (T T' : Over (Sp R)) (k : T' ⟶ T) (y : T ⟶ H), (Φ T' (k ≫ y)).b = k ≫ (Φ T y).b :=
    fun T T' k y => ((isPull_iff _ _ _).1 (hΦ.1 T' T k y)).1
  have gtan : ∀ y : epsR R ⟶ H, GtTan (Φ _ y) ↔ IsTangent y := by
    intro y
    rw [isTangent_iff]
    exact ⟨fun ⟨o, ho, h⟩ => (Φ _).injective ((isPull_unique (hΦ.1 _ _ (redO R) y) h).trans
      (GtVec.isZero_unique ho (hz _))), fun h => ⟨Φ _ 1, hz _, h ▸ hΦ.1 _ _ (redO R) y⟩⟩
  let β : (epsR R ⟶ H) →* (epsR R ⟶ D.P.A) :=
    { toFun := fun y => (Φ _ y).b
      map_one' := (hz _).1
      map_mul' := fun y y' => ((TorusModel.isAdd_iff _ _ _).1 (hΦ.2 _ y y')).1 }
  have βapp : ∀ y, β y = (Φ _ y).b := fun _ => rfl
  have βcomb : ∀ {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ H)),
      β (tanComb c v) = tanComb c (fun i => β (v i)) := by
    intro m c v
    simp only [tanComb, map_list_prod, List.map_ofFn]
    congr 1
    exact List.ofFn_inj.2 (funext fun i => bpull _ _ _ _)
  have βtan : ∀ y, IsTangent y → IsTangent (β y) := fun y h => (isTangent_iff _).2 (by
    rw [βapp, ← bpull, (isTangent_iff y).1 h]
    exact (hz _).1)
  have xtan : ∀ j, IsTangent (x j) := fun j => (gtan _).1 (htan j)
  have tor := GlobalTheory.T.torusTangentCombination_characterValues R D H Φ hΦ r (fun l χ => ((bX.repr χ l : ℤ) : R)) (fun l => x (Sum.inr l)) htor
  have split : ∀ c : Fin n → R, tanComb c (fun k => x (σ k)) =
      tanComb (fun i => c (σ.symm (Sum.inl i))) (fun i => x (Sum.inl i)) *
        tanComb (fun l => c (σ.symm (Sum.inr l))) (fun l => x (Sum.inr l)) := by
    intro c
    simp only [tanComb, List.prod_ofFn]
    have e := Equiv.prod_comp σ (fun j => epsScale R (c (σ.symm j)) ≫ x j)
    simp only [Equiv.symm_apply_apply] at e
    rw [e, Fintype.prod_sum_type]
  have βA : ∀ a : Fin D.P.g → R, β (tanComb a (fun i => x (Sum.inl i))) = tanComb a vB := by
    intro a
    rw [βcomb]
    simp only [βapp, hb]
  have βB : ∀ d : Fin r → R, β (tanComb d (fun l => x (Sum.inr l))) = 1 := fun d => (tor d).1
  have : IsLocalRing (DualNumber R) := GlobalTheory.MBLow.TanLift.isLocalRing_dualNumber R
  obtain ⟨J₀, hJ₀⟩ := TorusCoord.exists_good' D.P.isLB (cpt (DualNumber R))

  have uniq : ∀ c c' : Fin n → R, tanComb c (fun k => x (σ k)) = tanComb c' (fun k => x (σ k)) → c = c' := by
    intro c c' h
    rw [split, split] at h
    have hA := congrArg β h
    rw [map_mul, map_mul, βA, βA, βB, βB, _root_.mul_one, _root_.mul_one] at hA
    have ha : (fun i => c (σ.symm (Sum.inl i))) = (fun i => c' (σ.symm (Sum.inl i))) := by
      refine (hvB.2 _ (isTangent_tanComb _ hvB.1)).unique (isLieComb_tanComb _ _) ?_
      rw [hA]
      exact isLieComb_tanComb _ _
    rw [ha, mul_right_inj] at h
    have he : ∀ l, c (σ.symm (Sum.inr l)) = c' (σ.symm (Sum.inr l)) := by
      intro l
      have v1 := (tor (fun l => c (σ.symm (Sum.inr l)))).2 (bX l) _ (𝟙 _) _ J₀ hJ₀
      have v2 := (tor (fun l => c' (σ.symm (Sum.inr l)))).2 (bX l) _ (𝟙 _) _ J₀ hJ₀
      rw [h] at v1
      have := dn_inj (v1.symm.trans v2)
      simp only [Module.Basis.repr_self, Finsupp.single_apply] at this
      simpa using this
    funext k
    obtain ⟨j, rfl⟩ := σ.symm.surjective k
    rcases j with i | l
    · exact congrFun ha i
    · exact he l
  refine ⟨fun k => xtan (σ k), fun w hw => ?_⟩
  obtain ⟨c₁, hc₁, -⟩ := hvB.2 (β w) (βtan w hw)
  have hw₁ : β (tanComb c₁ (fun i => x (Sum.inl i))) = β w := by
    rw [βA]
    exact (eq_tanComb' hc₁).symm
  have tw' : IsTangent (w * (tanComb c₁ (fun i => x (Sum.inl i)))⁻¹) :=
    isTangent_mul hw (isTangent_inv (isTangent_tanComb _ fun i => xtan _))
  have bw' : (Φ _ (w * (tanComb c₁ (fun i => x (Sum.inl i)))⁻¹)).b = DegPre.zeroT D (epsR R) := by
    rw [← βapp, map_mul, map_inv, hw₁, mul_inv_cancel]
    rfl
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.torusExtensionTangent_characterValues_additive R D _ ((gtan _).2 tw') bw'
  have hl : ∀ χ, lam χ = ∑ l, lam (bX l) * ((bX.repr χ l : ℤ) : R) := by
    intro χ
    conv_lhs => rw [← bX.sum_repr χ]

    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  obtain ⟨bd, vd⟩ := tor (fun l => lam (bX l))
  have e : w * (tanComb c₁ (fun i => x (Sum.inl i)))⁻¹ = tanComb (fun l => lam (bX l)) (fun l => x (Sum.inr l)) :=
    (Φ _).injective (pt_ext (bw'.trans bd.symm) fun χ y J hJ => Units.ext ((hlam χ _ _ y J hJ).trans
      ((congrArg _ (by rw [hl χ])).trans (vd χ _ _ y J hJ).symm)))
  have hw : w = tanComb (fun k => Sum.elim c₁ (fun l => lam (bX l)) (σ k)) (fun k => x (σ k)) := by
    rw [split]
    simp only [Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr]
    rw [← e, mul_comm w, mul_inv_cancel_left]
  refine ⟨_, hw ▸ isLieComb_tanComb _ _, fun c hc => ?_⟩
  exact uniq _ _ ((eq_tanComb' hc).symm.trans hw)

end GlobalTheory.GtBasis

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisTorusExtensionOfLiftsAndDualsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.lieBasis_torusExtension_of_lifts_and_duals : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (H : Over (Sp R)) [GrpObj H] [IsCommMonObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ → ∀ (r : ℕ) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (bX : Module.Basis (Fin r) ℤ D.X) (x : Fin D.P.g ⊕ Fin r → (epsR R ⟶ H)), IsLieBasis vB → (∀ j, GtTan (Φ _ (x j))) → (∀ i, (Φ _ (x (Sum.inl i))).b = vB i) → (∀ l, (Φ _ (x (Sum.inr l))).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (x (Sum.inr l))).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr ((bX.repr χ l : ℤ) : R)))) → ∀ (n : ℕ) (σ : Fin n ≃ Fin D.P.g ⊕ Fin r), IsLieBasis (fun k => x (σ k)) := by
  first | exact @GlobalTheory.GtBasis.main | exact GlobalTheory.GtBasis.main | (intros; apply GlobalTheory.GtBasis.main <;> assumption) | exact @GlobalTheory.GtBasis.dn_inj | exact GlobalTheory.GtBasis.dn_inj | (intros; apply GlobalTheory.GtBasis.dn_inj <;> assumption)
end
end
