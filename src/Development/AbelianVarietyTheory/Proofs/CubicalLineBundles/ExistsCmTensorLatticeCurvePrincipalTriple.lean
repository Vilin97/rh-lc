module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmTensorSmoothOfRelativeDimension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalOfNormalised
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueCmHermitianLatticeFormStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivExternalTensorPowerLineBundle
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.NormNum.Parity
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleLineBundleOfPositiveHermitianCmFormStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorPairingIdentityOfPureTensors
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmTensorSmoothOfRelativeDimensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.cmTensor_smoothOfRelativeDimension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (b : OAct (OK H) A), Nonempty (Serre.IsTensor A b C.P.A C.act D.La) → SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) A.hom := by
  first | exact @GlobalTheory.CM.tensor_smoothOfRelativeDimension | exact GlobalTheory.CM.tensor_smoothOfRelativeDimension | (intros; apply GlobalTheory.CM.tensor_smoothOfRelativeDimension <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTensorBundle

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.TensorBundle

open GlobalTheory.PrimNorm GlobalTheory.MulPull GlobalTheory.Serre

section Algebra

variable {O V W U I : Type} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]
  [AddCommGroup U] [Fintype I]

def gramForm (β : V →+ V →+ U) (p : I → W →ₗ[O] V) (g : I → I → O) (x y : W) : U :=
  ∑ k : I × I, β (g k.1 k.2 • p k.1 x) (p k.2 y)

variable {β : V →+ V →+ U} {p : I → W →ₗ[O] V} {g : I → I → O} {br : O ≃+* O}

theorem gramForm_add_left (x y z : W) : gramForm β p g (x + y) z = gramForm β p g x z + gramForm β p g y z := by
  simp only [gramForm, map_add (f := _), smul_add, AddMonoidHom.add_apply, Finset.sum_add_distrib]

theorem gramForm_add_right (x y z : W) : gramForm β p g x (y + z) = gramForm β p g x y + gramForm β p g x z := by
  simp only [gramForm, map_add (f := _), Finset.sum_add_distrib]

theorem gramForm_zero (y : W) : gramForm β p g 0 y = 0 := by
  simp [gramForm]

theorem gramForm_adj (ha : ∀ c x y, β (c • x) y = β x (br c • y)) (c : O) (x y : W) :
    gramForm β p g (c • x) y = gramForm β p g x (br c • y) := by
  simp only [gramForm, map_smul]
  exact Finset.sum_congr rfl fun k _ => by rw [smul_comm, ha]

theorem gramForm_comm (hs : ∀ x y, β x y = β y x) (ha : ∀ c x y, β (c • x) y = β x (br c • y))
    (hg : ∀ i j, g j i = br (g i j)) (x y : W) : gramForm β p g x y = gramForm β p g y x :=
  Fintype.sum_equiv (Equiv.prodComm I I) _ _ fun k => by
    rw [ha, hs, ← hg]
    rfl

theorem gramForm_polar (hs : ∀ x y, β x y = β y x) (ha : ∀ c x y, β (c • x) y = β x (br c • y))
    (hg : ∀ i j, g j i = br (g i j)) {w : O} (hw : w + br w = 1) (x y : W) :
    gramForm β p g (x + y) (w • (x + y)) + -gramForm β p g x (w • x) + -gramForm β p g y (w • y) +
      gramForm β p g 0 (w • 0) = gramForm β p g x y := by
  have e : gramForm β p g x y = gramForm β p g x (w • y) + gramForm β p g y (w • x) := by
    rw [gramForm_comm hs ha hg y, gramForm_adj ha, ← gramForm_add_right, ← add_smul, hw, one_smul]
  rw [e, gramForm_zero, smul_add, gramForm_add_left, gramForm_add_right, gramForm_add_right]
  abel

theorem gramForm_pure (ha : ∀ c x y, β (c • x) y = β x (br c • y)) (hb : ∀ c, br (br c) = c)
    {x y : W} {u v : V} {s s' : I → O} (hx : ∀ i, p i x = s i • u) (hy : ∀ i, p i y = s' i • v) :
    gramForm β p g x y = β ((∑ k : I × I, br (s' k.2) * (g k.1 k.2 * s k.1)) • u) v := by

  rw [Finset.sum_smul, map_sum, AddMonoidHom.finsetSum_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [hx, hy, mul_smul (br _), ha (br _), hb, mul_smul]

theorem hermitian_expand {M : Type} [AddCommGroup M] [Module O M] (h : M →ₗ[O] M →+ O)
    (hh : ∀ x y, h y x = br (h x y)) (e : I → M) (s s' : I → O) :
    ∑ k : I × I, br (s' k.2) * (h (e k.1) (e k.2) * s k.1) = h (∑ i, s i • e i) (∑ i, s' i • e i) := by
  have sm : ∀ c x y, h x (c • y) = br c * h x y := fun c x y => by
    rw [hh (c • y) x, map_smul, AddMonoidHom.smul_apply, smul_eq_mul, map_mul, ← hh]

  rw [map_sum h, AddMonoidHom.finsetSum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sm, map_smul, AddMonoidHom.smul_apply, smul_eq_mul, mul_comm (s i)]

end Algebra

section Geometry

variable {S : Scheme.{0}} {O : Type} [CommRing O] {G A : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A]
  [IsCommMonObj A] {L : LB G.left}

def lamForm (a : OAct O G) (hL : L.IsLB) (hT : ∃ t : LB.Gen (Theta G L), t.IsGen) (T : Over S) :
    Pts a T →+ Pts a T →+ Additive (PullClass L T.left) :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => Additive.ofMul (diff₂ (ptCls L T) x.hom y.hom))
    fun y z => congrArg Additive.ofMul (diff₂_mul_right (diff₃_ptCls hL hT) x.hom y.hom z.hom))
    fun x y => AddMonoidHom.ext fun z => congrArg Additive.ofMul (diff₂_mul_left (diff₃_ptCls hL hT) x.hom y.hom z.hom)

variable {I : Type} [Fintype I]

def prodMap (f f' : I → (A ⟶ G)) (k : I × ULift.{0} (Finset (Fin 2))) : A.left ⟶ G.left :=
  (psum G ![f k.1, f' k.1] k.2.down).left

def prodExp (k : I × ULift.{0} (Finset (Fin 2))) : ℤ := (-1) ^ (2 - k.2.down.card)

def prodCls (L : LB G.left) (f f' : I → (A ⟶ G)) {Y : Scheme.{0}} (ψ : Y ⟶ A.left) : PullClass L Y :=
  ∏ k, cls L (ψ ≫ prodMap f f' k) ^ prodExp k

omit [GrpObj A] [IsCommMonObj A] in
theorem prodCls_left (f f' : I → (A ⟶ G)) {T : Over S} (x : T ⟶ A) :
    prodCls L f f' x.left = ∏ k, diff₂ (ptCls L T) (x ≫ f k) (x ≫ f' k) := by
  rw [prodCls, Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun k _ => prod_square x (f k) (f' k) (cls L)

end Geometry

theorem exists_tensor_bundle : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (M : Type) [AddCommGroup M] [Module O M] (t : Serre.IsTensor A b G a M) (br : O ≃+* O) (w : O) (L : LB G.left) (h : M →ₗ[O] M →+ O), Module.Finite O M → Module.Projective O M → w + br w = 1 → (∀ c, br (br c) = c) → (∀ x y, h y x = br (h x y)) → L.IsLB → (∃ t : LB.Gen (Theta G L), t.IsGen) → (∀ c, LamEq L (a.act c) (𝟙 G) L (𝟙 G) (a.act (br c))) →
  ∃ N : LB A.left, N.IsLB ∧ Out.Rigidified A N ∧ (∃ t : LB.Gen (Theta A N), t.IsGen) ∧ ∀ m m', LamEq N (t.tmul m) (t.tmul m') L (a.act (h m m')) (𝟙 G) := by
  intro S O _ G A _ _ _ _ a b M _ _ t br w L h _ _ hw hb hh hL hT ha
  obtain ⟨P⟩ := Summand.nonempty O M
  let c : Fin P.n → M →ₗ[O] O := fun i => LinearMap.proj i ∘ₗ P.incl
  let e : Fin P.n → M := fun i => P.proj (Pi.single i 1)
  have he : ∀ m, ∑ i, c i m • e i = m := fun m => by
    have : ∑ i, P.incl m i • (Pi.single i 1 : Fin P.n → O) = P.incl m := by
      ext j
      simp [Pi.single_apply]

    simp only [e, ← map_smul, ← map_sum]
    exact (congrArg P.proj this).trans congr($(P.proj_incl) m)
  let π : Fin P.n → (A ⟶ G) := fun i => t.mapLeft (IsTensor.self a) (c i)
  have hπ : ∀ i, IsLinearHom b a (π i) := fun i => t.isLinearHom_mapLeft _ _
  let g : Fin P.n → Fin P.n → O := fun i j => h (e i) (e j)
  let f : Fin P.n × Fin P.n → (A ⟶ G) := fun k => π k.1 ≫ a.act (g k.1 k.2)
  let f' : Fin P.n × Fin P.n → (A ⟶ G) := fun k => b.act w ≫ π k.2
  let B : ∀ T : Over S, Pts b T → Pts b T → Additive (PullClass L T.left) := fun T =>
    gramForm (lamForm a hL hT T) (fun i => Pts.post (hπ i) T) g
  have hs : ∀ (T : Over S) x y, lamForm a hL hT T x y = lamForm a hL hT T y x := fun T x y =>
    congrArg Additive.ofMul (diff₂_comm _ _)
  have hadj : ∀ (T : Over S) (r : O) x y, lamForm a hL hT T (r • x) y = lamForm a hL hT T x (br r • y) :=
    fun T r x y => by
      have := ha r
      unfold LamEq at this
      rw [Category.comp_id, Category.comp_id] at this
      exact congrArg Additive.ofMul (diff₂_ptCls_adj hL this x.hom y.hom)
  have hq : ∀ (T : Over S) (x : T ⟶ A), prodCls L f f' x.left = (B T (Pts.mk b x) (w • Pts.mk b x)).toMul :=
    fun T x => by
      rw [prodCls_left]
      refine Eq.trans (Finset.prod_congr rfl fun k _ => ?_) (toMul_sum _ _).symm
      simp only [f, f', ← Category.assoc]
      rfl
  have h₂ : ∀ (T : Over S) (x y : T ⟶ A), diff₂ (fun q : T ⟶ A => prodCls L f f' q.left) x y =
      (B T (Pts.mk b x) (Pts.mk b y)).toMul := fun T x y => by
    simp only [diff₂, hq]
    exact congrArg Additive.toMul (gramForm_polar (hs T) (hadj T) (fun i j => hh _ _) hw (Pts.mk b x) (Pts.mk b y))
  refine ⟨LB.LinComb L (prodMap f f') prodExp, DVR.linComb_isLB _ hL _ _, ?_, ?_, fun m m' => ?_⟩
  · refine hasGen_nested (K' := PUnit) hL _ _ (fun _ => eSec A) (fun _ => 1) ?_
    rw [Fintype.prod_unique, zpow_one]
    refine (hq _ η[A]).trans ?_
    have e : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by simp [Hom.one_def]
    rw [e]
    exact congrArg Additive.toMul (gramForm_zero _)
  · refine hasGen_nested hL _ _ (thφ A (x3 A)) thε ((GlobalTheory.AbLaw.Cube.prod_theta (prodCls L f f')).trans
      ((prod_cub _ _ _ (prodCls L f f')).trans ?_))
    have e := diff₂_mul_left_eq (m := fun q : G3 A ⟶ A => prodCls L f f' q.left) (x3 A 0) (x3 A 1) (x3 A 2)
    rw [h₂, h₂, h₂, Pts.mk_mul] at e
    exact mul_eq_right.1 (e.symm.trans (congrArg Additive.toMul (gramForm_add_left _ _ _)))
  · refine lbIso_nested hL _ _ _ _ _ _ ((prod_square_id _ _ (prodCls L f f')).trans
      (Eq.trans ?_ (prod_square_id _ _ (cls L)).symm))
    have k : ∀ (u : G ⊗ G ⟶ G) (m : M) i,
        Pts.post (hπ i) _ (Pts.mk b (u ≫ t.tmul m)) = c i m • Pts.mk a u := fun u m i => Pts.ext (by
      simp only [Pts.hom_post, Pts.hom_mk, Pts.hom_smul, π, Category.assoc, IsTensor.tmul_mapLeft,
        IsTensor.self_tmul])
    rw [h₂, Category.comp_id]
    refine congrArg Additive.toMul ((gramForm_pure (hadj _) hb (k _ m) (k _ m')).trans ?_)
    rw [(hermitian_expand h hh e (fun i => c i m) fun i => c i m' :
      ∑ k : Fin P.n × Fin P.n, br (c k.2 m') * (g k.1 k.2 * c k.1 m) = _), he, he]
    rfl

end GlobalTheory.TensorBundle
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KTrivOfUnimodular

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.HermTensorKernel

open GlobalTheory.CechPic

section Local

variable {Y Y' B : Scheme.{0}}

def LocZero (π : Y ⟶ B) (c : Pic Y) : Prop :=
  ∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ Y), (∀ z, π (f z) ∈ V) → pull f c = 0

theorem LocZero.add {π : Y ⟶ B} {c d : Pic Y} (hc : LocZero π c) (hd : LocZero π d) : LocZero π (c + d) := by
  intro p
  obtain ⟨V, hV, H⟩ := hc p
  obtain ⟨V', hV', H'⟩ := hd p
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, fun Z f hf => ?_⟩
  rw [map_add (f := _), H Z f fun z => (hf z).1, H' Z f fun z => (hf z).2, add_zero]

theorem LocZero.pull {π : Y ⟶ B} {c : Pic Y} (hc : LocZero π c) (k : Y' ⟶ Y) :
    LocZero (k ≫ π) (pull k c) := by
  intro p
  obtain ⟨V, hV, H⟩ := hc p
  exact ⟨V, hV, fun Z f hf => (pull_comp f k c).symm.trans (H Z (f ≫ k) hf)⟩

theorem locZero_base (π : Y ⟶ B) (d : Pic B) : LocZero π (pull π d) := by
  obtain ⟨D, hD, rfl⟩ := cls_surj d
  intro p
  obtain ⟨i, hi⟩ := exists_chart hD p
  refine ⟨D.U i, hi, fun Z f hf => (pull_comp f π _).symm.trans ?_⟩
  exact (cls_eq_zero_iff (pull_isLB hD (f ≫ π))).2
    (BoxKernel.gen_of_chart (pull_isLB hD _) (fun _ => i) fun z => mem_pull.2 (hf z))

theorem locZero_iff (π : Y ⟶ B) {M : LB Y} (hM : M.IsLB) :
    (∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∃ c : LB.Gen (M.pull (π ⁻¹ᵁ V).ι), c.IsGen) ↔ LocZero π (cls M hM) := by
  refine forall_congr' fun p => exists_congr fun V => and_congr_right fun _ => ?_
  rw [← cls_eq_zero_iff (pull_isLB hM _), cls_pull hM]
  refine ⟨fun H Z f hf => ?_, fun H => H _ _ fun z => z.2⟩
  have hr : Set.range f ⊆ Set.range (π ⁻¹ᵁ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hf z
  rw [← IsOpenImmersion.lift_fac (π ⁻¹ᵁ V).ι f hr, pull_comp, H, map_zero]

end Local

section Group

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A]

theorem translDiff_iff {L : LB A.left} (hL : L.IsLB) (x : T ⟶ A) :
    (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((Out.translDiff A L x).pull ((fst T A).left ⁻¹ᵁ V).ι), c.IsGen) ↔
      LocZero (fst T A).left (lam (cls L hL) (fst T A ≫ x) (snd T A)) := by
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  rw [locZero_iff _ hD]
  have e : lam (cls L hL) (fst T A ≫ x) (snd T A) = cls _ hD +
      pull (fst T A).left (pull (1 : T ⟶ A).left (cls L hL) - pull x.left (cls L hL)) := by
    have e₁ : cls _ hD = pull ((fst T A ≫ x) * snd T A).left (cls L hL) - pull (snd T A).left (cls L hL) := by
      refine (cls_linComb hL _ _ hD).trans ?_
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, ← sub_eq_add_neg]
      rfl
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one, lam]
    abel
  refine ⟨fun H => e ▸ H.add (locZero_base _ _), fun H => ?_⟩
  have := H.add (locZero_base _ (-(pull (1 : T ⟶ A).left (cls L hL) - pull x.left (cls L hL))))
  rwa [e, map_neg, add_neg_cancel_right] at this

end Group

end GlobalTheory.HermTensorKernel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KTrivOfPerfect

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.PerfectTensorKernel

open GlobalTheory.CechPic GlobalTheory.HermTensorKernel GlobalTheory.Serre

theorem kTriv_of_perfect : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (M : Type) [AddCommGroup M] [Module O M] (t : Serre.IsTensor A b G a M) (L : LB G.left) (N : LB A.left) (h : M →ₗ[O] M →+ O) (n : ℕ) (x y : Fin n → M), (∀ m, m = ∑ i, h m (y i) • x i) → L.IsLB → N.IsLB → (∃ t : LB.Gen (Theta G L), t.IsGen) → (∃ t : LB.Gen (Theta A N), t.IsGen) → (∀ m m', LamEq N (t.tmul m) (t.tmul m') L (a.act (h m m')) (𝟙 G)) → Out.KTriv G L → Out.KTriv A N := by
  intro S O _ G A _ _ _ _ a b M _ _ t L N h n x₀ y₀ hdual hL hN hΘL hΘ hiso hK R _ s x hx
  have am := a.hom
  let l : M → (M →ₗ[O] O) := fun n =>
    { toFun := fun m => h m n
      map_add' := fun m m' => by rw [map_add (f := _), AddMonoidHom.add_apply]
      map_smul' := fun c m => by rw [map_smul, AddMonoidHom.smul_apply, RingHom.id_apply] }
  let q : M → (A ⟶ G) := fun n => t.mapLeft (IsTensor.self a) (l n)
  have qm : ∀ n, IsMonHom (q n) := fun n => IsTensor.isMonHom_mapLeft _ _ _
  have hq : ∀ m n, t.tmul m ≫ q n = a.act (h m n) := fun m n => by
    simp only [q, IsTensor.tmul_mapLeft, IsTensor.self_tmul]
    rfl
  have basic : ∀ {T : Over S} (g y : T ⟶ G) (m n : M),
      lam (cls N hN) (g ≫ t.tmul m) (y ≫ t.tmul n) = lam (cls L hL) (g ≫ a.act (h m n)) y := by
    intro T g y m n
    have h₀ := (cls_eq_iff (LB.isLB_linComb hN _ _) (LB.isLB_linComb hL _ _)).2 (hiso m n)
    have h' := congrArg (pull (lift g y).left)
      ((cls_cube_two hN _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.comp_id] using h'
  have key : ∀ {T : Over S} (n : M) (u : T ⟶ A) (y : T ⟶ G),
      lam (cls N hN) u (y ≫ t.tmul n) = lam (cls L hL) (u ≫ q n) y := by
    intro T n u y
    refine t.induction_on (P := fun u =>
      lam (cls N hN) u (y ≫ t.tmul n) = lam (cls L hL) (u ≫ q n) y) u ?_ (fun m g => ?_)
      fun u v hu hv => ?_
    · rw [MonObj.one_comp, lam_one_left, lam_one_left]
    · rw [Category.assoc, hq, basic]
    · rw [lam_mul_left hN hΘ, hu, hv, MonObj.mul_comp, lam_mul_left hL hΘL]
  have H := (translDiff_iff hN x).1 hx
  have z : ∀ n, x ≫ q n = 1 := fun n => by
    refine hK R s _ ((translDiff_iff hL (x ≫ q n)).2 ?_)
    have H' := H.pull (Over.mk s ◁ t.tmul n).left
    rwa [pull_lam, ← Over.comp_left, whiskerLeft_fst, whiskerLeft_fst_assoc, whiskerLeft_snd, key,
      Category.assoc] at H'
  have dec : ∀ u : Over.mk s ⟶ A, u = ∏ i, (u ≫ q (y₀ i)) ≫ t.tmul (x₀ i) := by
    intro u
    refine t.induction_on (P := fun u => u = ∏ i, (u ≫ q (y₀ i)) ≫ t.tmul (x₀ i)) u ?_
      (fun m g => ?_) fun u v hu hv => ?_
    · simp only [MonObj.one_comp, Finset.prod_const_one]
    · simp only [Category.assoc, reassoc_of% hq, ← t.tmul_smul']
      refine Eq.trans ?_ (map_prod (preHom g) _ _)
      rw [← t.tmul_sum, ← hdual]
      rfl
    · simp only [MonObj.mul_comp, Finset.prod_mul_distrib, ← hu, ← hv]
  rw [dec x]
  simp only [z, MonObj.one_comp, Finset.prod_const_one]
  rfl

end GlobalTheory.PerfectTensorKernel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmTensorLatticeCurvePrincipalTriple

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM

theorem exists_isTen : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → ∃ T : PAT H (Sp R), Nonempty (IsTen C D h T) ∧ T.g = Module.finrank ℚ E / 2 * (D.p + D.q) := by
  intro laws E _ _ _ H R _ _ ω C D ε h hK hpos
  obtain ⟨h₀, -, huniq, hbar, hE, -, -, n, x, y, hxy⟩ := GlobalTheory.T.exists_unique_cmHermitianLatticeForm E H D ε
  obtain rfl := huniq h hK
  obtain ⟨-, -, ⟨br, hbr, hw, hbb⟩, -, -, hM⟩ := OK_isDedekindDomain_and_projective E H
  obtain ⟨hfin, hproj, -⟩ := hM D.La D.fin D.proj
  let t := Serre.isTensor D.La C.act
  obtain ⟨c, τ, hc⟩ : ∃ (c : OAct (𝓞 E) (Serre.tensorObj D.La C.act))
      (τ : Serre.IsTensor _ (Serre.comapAct c (algebraMap (OK H) (𝓞 E))) C.P.A C.act D.La),
      ∀ (s : 𝓞 E) a, τ.tmul (s • a) = τ.tmul a ≫ c.act s := by
    have key : ∀ b', b' = Serre.tensorAct D.La C.act → ∃ τ : Serre.IsTensor _ b' C.P.A C.act D.La,
        ∀ a, τ.tmul a = t.tmul a := by
      rintro _ rfl
      exact ⟨t, fun _ => rfl⟩
    obtain ⟨τ, hτ⟩ := key _ (t.comapAct_algAct (𝓞 E))
    exact ⟨t.algAct (𝓞 E), τ, fun s a => by rw [hτ, hτ, t.tmul_algAct]⟩
  have hA : IsAbelianScheme (Serre.tensorObj D.La C.act) := τ.isAbelianScheme C.P.isAb
  obtain ⟨rig, hrig⟩ := C.P.rigid
  obtain ⟨cubP⟩ := (laws.cube _ C.P ⟨C.P.L, rig, C.P.isLB, hrig⟩ rfl).1
  have hθP : ∃ t : LB.Gen (Theta C.P.A C.P.L), t.IsGen := ⟨cubP.t, cubP.isGen⟩
  obtain ⟨N, hN, -, hθ, hp⟩ := GlobalTheory.TensorBundle.exists_tensor_bundle _ (OK H) C.P.A _ C.act _ D.La τ br (wK H) C.P.L h₀
    hfin hproj hw hbb (fun a b => Subtype.ext ((hbar a b).trans (hbr _).symm)) C.P.isLB hθP
    (fun a => C.adj a (br a) (hbr a))
  obtain ⟨PP, cub, sym, -, hΛ, prim, adj⟩ := GlobalTheory.PrimNorm.exists_primitive_normalisation laws.globalFns E H _ _ c N
    hA hN hθ fun s => by
      have := GlobalTheory.LamCalc.lamEq_of_tmul _ (OK H) C.P.A _ C.act _ D.La τ _ _ D.La τ _ _ N N (c.act s) (𝟙 _) (𝟙 _)
        (c.act (H.bar s)) hN hN hθ hθ (c.hom _) inferInstance inferInstance (c.hom _) fun m m' => by
          rw [← hc, ← hc, Category.comp_id, Category.comp_id]
          have a := hp (s • m) m'
          rw [hE] at a
          exact LBIso.trans (DVR.linComb_isLB _ hN _ _) (DVR.linComb_isLB _ C.P.isLB _ _) (DVR.linComb_isLB _ hN _ _)
            a (hp m (H.bar s • m')).symm
      simpa only [LamEq, Category.comp_id] using this
  have hp' : ∀ m m', LamEq PP.L (τ.tmul m) (τ.tmul m') C.P.L (C.act.act (h₀ m m')) (𝟙 C.P.A) := fun m m' =>
    LBIso.trans (DVR.linComb_isLB _ PP.isLB _ _) (DVR.linComb_isLB _ hN _ _) (DVR.linComb_isLB _ C.P.isLB _ _)
      (hΛ.chartPull
        (GlobalTheory.PrimNorm.chartSquare PP.L (lift (fst C.P.A C.P.A ≫ τ.tmul m) (snd C.P.A C.P.A ≫ τ.tmul m'))
          (lift_fst _ _).symm (lift_snd _ _).symm)
        (GlobalTheory.PrimNorm.chartSquare N (lift (fst C.P.A C.P.A ≫ τ.tmul m) (snd C.P.A C.P.A ≫ τ.tmul m'))
          (lift_fst _ _).symm (lift_snd _ _).symm))
      (hp m m')
  have hθ' : ∃ t : LB.Gen (Theta _ PP.L), t.IsGen := ⟨cub.t, cub.isGen⟩
  let s : SAB H (Sp R) :=
    { G := Serre.tensorObj D.La C.act, semi := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hA, act := c, PP := PP,
      cub := cub, sym := sym, adj := adj, prim := prim }
  exact ⟨⟨s, hA, _, GlobalTheory.T.cmTensor_smoothOfRelativeDimension E H R ω C D _ _ ⟨τ⟩, ObjDim.sym,
    GlobalTheory.T.relAmple_lineBundle_of_positive_hermitian_cm_form laws E H R ω C D ε _ _ _ τ PP.L hK hpos PP.isLB hθ' prim hp',
    GlobalTheory.PerfectTensorKernel.kTriv_of_perfect _ (OK H) C.P.A _ C.act _ D.La τ C.P.L PP.L h₀ n x y hxy C.P.isLB PP.isLB
      hθP hθ' hp' C.P.ktriv⟩, ⟨⟨τ, hc, hp'⟩⟩, rfl⟩

end GlobalTheory.CM
end
end
end
