module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Mathlib.Algebra.Homology.ShortComplex.Ab
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
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.ShortComplex.Ab

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingCofaceComplexOfFunctorDZeroOne

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.CartanStep
variable {T : Type 1} [Category.{0} T]

abbrev altCx (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) : CochainComplex AddCommGrpCat.{1} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ F)

theorem alternatingCofaceComplexOfFunctor_d_zero_one (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) (y : F.obj (X.obj (SimplexCategory.mk 0))) :
    (altCx X F).d 0 1 y = F.map (X.δ (n := 0) 0) y - F.map (X.δ (n := 0) 1) y := by
  have h0 : (altCx X F).d 0 1 = AlgebraicTopology.AlternatingCofaceMapComplex.objD (X ⋙ F) 0 :=
    CochainComplex.of_d (fun n ↦ (X ⋙ F).obj (SimplexCategory.mk n)) (AlgebraicTopology.AlternatingCofaceMapComplex.objD (X ⋙ F)) 0
  rw [h0]
  simp [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_two, sub_eq_add_neg, CosimplicialObject.δ]
  rfl

theorem altCx_nat (X : CosimplicialObject T) {F G : T ⥤ AddCommGrpCat.{1}} (φ : F ⟶ G) (n m : ℕ)
    (w : F.obj (X.obj (SimplexCategory.mk n))) :
    (altCx X G).d n m (φ.app _ w) = φ.app _ ((altCx X F).d n m w) := by
  have h := ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).map (Functor.whiskerLeft X φ)).comm n m
  exact ConcreteCategory.congr_hom h w

theorem altCx_dd (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) (y : F.obj (X.obj (SimplexCategory.mk 0))) :
    (altCx X F).d 1 2 ((altCx X F).d 0 1 y) = 0 :=
  ConcreteCategory.congr_hom ((altCx X F).d_comp_d 0 1 2) y

theorem altCx_exact1 (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) (h : (altCx X F).ExactAt 1)
    (w : F.obj (X.obj (SimplexCategory.mk 1))) (hw : (altCx X F).d 1 2 w = 0) :
    ∃ v : F.obj (X.obj (SimplexCategory.mk 0)), (altCx X F).d 0 1 v = w := by
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp), ShortComplex.ab_exact_iff] at h
  exact h w hw

theorem aug_δ {U : T} {X : CosimplicialObject T} (a : (CosimplicialObject.const T).obj U ⟶ X) (j : Fin 2) :
    a.app (SimplexCategory.mk 0) ≫ X.δ j = a.app (SimplexCategory.mk 1) := by
  have h := a.naturality (SimplexCategory.δ j)
  simpa [CosimplicialObject.δ] using h.symm

theorem cartan_step : ∀ (T : Type 1) [Category.{0} T] (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X) (Z M N : T ⥤ AddCommGrpCat.{1}) (i : Z ⟶ M) (d : M ⟶ N), (∀ V, Function.Injective (i.app V)) → (∀ V (y : M.obj V), d.app V y = 0 ↔ ∃ w, i.app V w = y) → WExact M a → WExact N a → ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ Z)).ExactAt 1 → ∀ (z : N.obj U) (y : M.obj (X.obj (SimplexCategory.mk (0)))), d.app _ y = N.map (a.app (SimplexCategory.mk (0))) z → ∃ x : M.obj U, d.app U x = z := by
  intro T _ U X a Z M N i d hi hd hM hN hZ z y hy
  have hu : d.app _ ((altCx X M).d 0 1 y) = 0 := by
    rw [alternatingCofaceComplexOfFunctor_d_zero_one, map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply, hy,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← N.map_comp, ← N.map_comp,
      aug_δ a 0, aug_δ a 1, sub_self]
  obtain ⟨w, hw⟩ := (hd _ _).1 hu
  have hw2 : (altCx X Z).d 1 2 w = 0 := by
    have h1 : i.app _ ((altCx X Z).d 1 2 w) = 0 := by
      rw [← altCx_nat X i 1 2 w, hw, altCx_dd]
      rfl
    exact hi _ (h1.trans (map_zero _).symm)
  obtain ⟨v, hv⟩ := altCx_exact1 X Z hZ w hw2
  have hy' : M.map (X.δ (n := 0) 0) (y - i.app _ v) = M.map (X.δ (n := 0) 1) (y - i.app _ v) := by
    rw [← sub_eq_zero, map_sub, map_sub, sub_sub_sub_comm, ← alternatingCofaceComplexOfFunctor_d_zero_one, ← alternatingCofaceComplexOfFunctor_d_zero_one, altCx_nat X i 0 1, hv, hw]
    exact sub_self _
  obtain ⟨x, hx⟩ := hM.2.1 _ hy'
  refine ⟨x, hN.1 ?_⟩
  have e := ConcreteCategory.congr_hom (d.naturality (a.app (SimplexCategory.mk 0))) x
  simp only [ConcreteCategory.comp_apply] at e
  have e2 : d.app (X.obj (SimplexCategory.mk 0)) (y - i.app _ v) = N.map (a.app (SimplexCategory.mk 0)) z := by
    rw [map_sub, hy, (hd _ _).2 ⟨v, rfl⟩, sub_zero]
  rw [← hx] at e2
  exact e.symm.trans e2

end GlobalTheory.CartanStep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosimplicialSesExactAtSucc

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem cosimplicial_ses_exactAt_succ :
    ∀ (Z M Q : CosimplicialObject AddCommGrpCat.{1}) (i : Z ⟶ M) (p : M ⟶ Q), (∀ k, Function.Injective (i.app k)) → (∀ k (y : M.obj k), p.app k y = 0 ↔ ∃ w, i.app k w = y) → (∀ k, Function.Surjective (p.app k)) → (∀ n : ℕ, ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj Z).ExactAt (n + 1)) → (∀ n : ℕ, ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj M).ExactAt (n + 1)) → ∀ n : ℕ, ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj Q).ExactAt (n + 1) := by
  intro Z M Q i p hinj hex hsurj h₁ h₂
  let F := AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}
  have hw : F.map i ≫ F.map p = 0 := by
    ext k y
    exact (hex _ (i.app _ y)).2 ⟨y, rfl⟩
  let T : ShortComplex (CochainComplex AddCommGrpCat.{1} ℕ) := ShortComplex.mk (F.map i) (F.map p) hw
  have hT : T.ShortExact := by
    refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun k => ?_
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.ab_exact_iff]; intro x hx; exact (hex _ x).1 hx
    · rw [AddCommGrpCat.mono_iff_injective]; exact hinj _
    · rw [AddCommGrpCat.epi_iff_surjective]; exact hsurj _
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have e := hT.homology_exact₃ (n + 1) (n + 2) rfl
  have z2 : IsZero (T.X₂.homology (n + 1)) := (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₂ n)
  have z1 : IsZero (T.X₁.homology (n + 2)) := (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₁ (n + 1))
  exact e.isZero_X₂ (z2.eq_of_src _ _) (z1.eq_of_tgt _ _)

end GlobalTheory.EtC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanZero

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.CartanZero
variable {T : Type 1} [Category.{0} T]

def cyc (C : T ⥤ AbCx) (i j : ℤ) : T ⥤ AddCommGrpCat.{1} where
  obj U := AddCommGrpCat.of ((C.obj U).d i j).hom.ker
  map {U V} f := AddCommGrpCat.ofHom
    { toFun := fun x => ⟨(C.map f).f i x.1, by
        have e := ConcreteCategory.congr_hom ((C.map f).comm i j) x.1
        simp only [ConcreteCategory.comp_apply] at e
        change (C.obj V).d i j ((C.map f).f i x.1) = 0
        rw [e, show (C.obj U).d i j x.1 = 0 from x.2, map_zero]⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  map_id U := by ext x; simp
  map_comp f g := by ext x; simp

def incl (C : T ⥤ AbCx) (i j : ℤ) : cyc C i j ⟶ term C i where
  app U := AddCommGrpCat.ofHom (AddSubgroup.subtype _)
  naturality U V f := by ext x; rfl

def dN (C : T ⥤ AbCx) (i j : ℤ) : term C i ⟶ term C j where
  app U := (C.obj U).d i j
  naturality U V f := (C.map f).comm i j

def pN (C : T ⥤ AbCx) (i j k : ℤ) : term C i ⟶ cyc C j k where
  app U := AddCommGrpCat.ofHom
    { toFun := fun y => ⟨(C.obj U).d i j y, by
        change (C.obj U).d j k ((C.obj U).d i j y) = 0
        exact ConcreteCategory.congr_hom ((C.obj U).d_comp_d i j k) y⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  naturality U V f := by
    ext y
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((C.map f).comm i j) y

end GlobalTheory.CartanZero

namespace GlobalTheory.CartanZero
variable {T : Type 1} [Category.{0} T]

def Good (C : T ⥤ AbCx) (j : ℤ) : Prop :=
  ∀ i, i + 1 = j → ∀ (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X),
    (∀ n, WExact (term C n) a) → ∀ k : ℕ,
      ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ cyc C i j)).ExactAt (k + 1)

theorem good_of_le (C : T ⥤ AbCx) (b : ℤ) (hb : ∀ n : ℤ, n < b → ∀ U, IsZero ((C.obj U).X n))
    (j : ℤ) (hj : j ≤ b) : Good C j := by
  intro i hi U X a _ k
  have hs : ∀ V, Subsingleton ((cyc C i j).obj V) := fun V => by
    have : Subsingleton ((C.obj V).X i) := AddCommGrpCat.subsingleton_of_isZero (hb i (by omega) V)
    change Subsingleton (((C.obj V).d i j).hom.ker)
    infer_instance
  rw [HomologicalComplex.exactAt_iff' _ k (k + 1) (k + 2) (by simp) (by simp), ShortComplex.ab_exact_iff]
  intro x _
  exact ⟨0, (hs _).elim _ _⟩

theorem step (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) (C : T ⥤ AbCx)
    (hR : Refines Cov (fun U X a => ∀ n, WExact (term C n) a)) (hL : LocExact Cov C)
    (j : ℤ) (hG : Good C j) (U : T) (z : (C.obj U).X j) (hz : (C.obj U).d j (j + 1) z = 0) :
    ∃ y : (C.obj U).X (j - 1), (C.obj U).d (j - 1) j y = z := by
  obtain ⟨V, g, hg, y, hy⟩ := hL j U z hz
  obtain ⟨X, a, h, hgh, hW⟩ := hR U V g hg
  have hZ := hG (j - 1) (by omega) U X a hW 0
  refine GlobalTheory.CartanStep.cartan_step T U X a (cyc C (j - 1) j) (term C (j - 1)) (term C j) (incl C (j - 1) j)
    (dN C (j - 1) j) (fun V => Subtype.val_injective) (fun V y => ⟨fun h => ⟨⟨y, h⟩, rfl⟩, ?_⟩) (hW _) (hW _) hZ z
    ((C.map h).f (j - 1) y) ?_
  · rintro ⟨w, rfl⟩
    exact w.2
  · change (C.obj _).d (j - 1) j ((C.map h).f (j - 1) y) = (C.map (a.app _)).f j z
    have e := ConcreteCategory.congr_hom ((C.map h).comm (j - 1) j) y
    simp only [ConcreteCategory.comp_apply] at e
    rw [e, hy, ← hgh, Functor.map_comp, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]

end GlobalTheory.CartanZero

namespace GlobalTheory.CartanZero

theorem good_succ (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) (C : T ⥤ AbCx)
    (hR : Refines Cov (fun U X a => ∀ n, WExact (term C n) a)) (hL : LocExact Cov C)
    (j : ℤ) (hG : Good C j) : Good C (j + 1) := by
  intro i hi U X a hW
  obtain rfl : i = j := by omega
  refine cosimplicial_ses_exactAt_succ (X ⋙ cyc C (i - 1) i) (X ⋙ term C (i - 1)) (X ⋙ cyc C i (i + 1))
    (Functor.whiskerLeft X (incl C (i - 1) i)) (Functor.whiskerLeft X (pN C (i - 1) i (i + 1)))
    (fun k => Subtype.val_injective) (fun k y => ⟨fun h => ⟨⟨y, congrArg Subtype.val h⟩, rfl⟩, ?_⟩) ?_
    (hG (i - 1) (by omega) U X a hW) (hW (i - 1)).2.2
  · rintro ⟨w, rfl⟩
    exact Subtype.ext w.2
  · intro k c
    obtain ⟨y, hy⟩ := step T Cov C hR hL i hG (X.obj k) c.1 c.2
    exact ⟨y, Subtype.ext hy⟩

theorem cartan_zero : ∀ (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) (C : T ⥤ AbCx), (∃ b : ℤ, ∀ n : ℤ, n < b → ∀ U, IsZero ((C.obj U).X n)) → Refines Cov (fun U X a => ∀ n, WExact (term C n) a) → LocExact Cov C → ∀ (U : T) (n : ℤ) (z : (C.obj U).X n), (C.obj U).d n (n + 1) z = 0 → ∃ y : (C.obj U).X (n - 1), (C.obj U).d (n - 1) n y = z := by
  intro T _ Cov C ⟨b, hb⟩ hR hL U n z hz
  have hall : ∀ t : ℕ, Good C (b + t) := by
    intro t
    induction t with
    | zero => simpa using good_of_le C b hb b le_rfl
    | succ t ih =>
      have := good_succ T Cov C hR hL _ ih
      simpa [add_assoc] using this
  have hGn : Good C n := by
    by_cases h : n ≤ b
    · exact good_of_le C b hb n h
    · have e : b + ((n - b).toNat : ℤ) = n := by omega
      have h2 := hall (n - b).toNat
      rw [e] at h2
      exact h2
  exact step T Cov C hR hL n hGn U z hz

end GlobalTheory.CartanZero
end
end
