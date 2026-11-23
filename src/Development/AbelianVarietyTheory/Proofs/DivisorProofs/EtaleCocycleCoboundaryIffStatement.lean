module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyOneCechCocycleOfPullbackZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyPullbackEqZeroOfCechOneCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicProperties
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeSheafHomValueAtCechNerveSimplexBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainCoboundaryOfClassZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSurjectiveCechDescentCohomologyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleTensorWidePullbackLimitStatement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyPullbackEqZeroOfCechOneCocycleStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

theorem _root_.GlobalTheory.T.etaleCohomologyPullback_eq_zero_of_cechOneCocycle :
    ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X)
      (s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F),
      cobd (R := R) (E := cech f) (n := 1) s = 0 →
      ∀ x : H R (sch.obj X) F ((1 : ℕ) : ℤ),
        IsCls (R := R) (E := cech f) (n := 1) s (pull R (cechAug f) F ((1 : ℕ) : ℤ) x) →
        pull R (sch.map f) F ((1 : ℕ) : ℤ) x = 0 := by
  intro R _ F Y X f s hs x hx
  have hc := congrArg (fun t => (free R).map ((cechDiag f).app (op ⦋2⦌)) ≫ t) hs
  simp only [cobd, Preadditive.comp_sum, Preadditive.comp_zsmul, ← Functor.map_comp_assoc,
    cechDiag_δ, comp_zero] at hc
  have hc' : ((free R).map ((cechDiag f).app (op ⦋1⦌)) ≫ s :
      (free R).obj ((sch.obj Y).obj (op ⦋2⦌)) ⟶ F) = 0 := by
    simpa [Fin.sum_univ_succ] using hc
  have hd : (free R).map ((cechDiag f).app (op ⦋1⦌)) ≫ s = 0 := hc'
  obtain ⟨z, hzClass, hz⟩ := hx
  rw [← cechDiag_aug f, pull_comp, ← hzClass]
  simp only [pull, HK.pull, HK.pre, cpre_mk]
  rw [← CohomologyClass.mk_zero]
  apply congrArg CohomologyClass.mk
  apply Cocycle.ext
  change (Cochain.ofHom ((chains R).map (cechDiag f))).comp z.1 (zero_add _) = 0
  rw [hz, ClsBasic.ofHom_comp_single]
  simp only [← Category.assoc, ClsBasic.chainsXIso_nat]
  simp [Category.assoc, hd]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitWidePullbackConeSpecSingle

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

namespace GlobalTheory.CechOne

theorem isLimit_cone_one (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (0 + 1) => GlobalTheory.CechOne.fB A B)
      (GlobalTheory.CechOne.fB A B) (fun _ => 𝟙 _) (fun _ => Category.id_comp _))) := by
  refine ⟨WidePullbackCone.IsLimit.mk _ (fun t => t.π 0) ?_ ?_ ?_⟩
  · intro t
    rw [WidePullbackCone.mk_base]
    exact t.condition 0
  · intro t i
    rw [WidePullbackCone.mk_π]
    exact (Category.comp_id (t.π 0)).trans (congrArg t.π (Fin.fin_one_eq_zero i).symm)
  · intro t m _ hπ
    have := hπ 0
    rw [WidePullbackCone.mk_π] at this
    exact (Category.comp_id m).symm.trans this

end GlobalTheory.CechOne
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitWidePullbackConeSpecSingleStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

theorem _root_.GlobalTheory.T.isLimit_widePullbackCone_spec_single : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (0 + 1) => GlobalTheory.CechOne.fB A B) (GlobalTheory.CechOne.fB A B) (fun _ => 𝟙 _) (fun _ => Category.id_comp _))) := by
  first | (exact @GlobalTheory.CechOne.isLimit_cone_one) | (exact GlobalTheory.CechOne.isLimit_cone_one) | (intros; apply GlobalTheory.CechOne.isLimit_cone_one  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitWidePullbackConeSpecTensorSquare

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

noncomputable section
namespace GlobalTheory.CechOne

theorem isLimit_widePullback_tensor (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (1 + 1) => GlobalTheory.CechOne.fB A B)
      (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B)))) (GlobalTheory.CechOne.y1 A B) (GlobalTheory.CechOne.hy1 A B))) := by
  have H := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A B B)
  have e0 : y1 A B 0 = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := rfl
  have e1 : y1 A B 1 = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) := rfl
  refine ⟨WidePullbackCone.IsLimit.mk _ (fun t => H.lift (t.π 0) (t.π 1) ?_) ?_ ?_ ?_⟩
  · exact (t.condition 0).trans (t.condition 1).symm
  · intro t
    change _ ≫ Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B))) = _
    rw [← hy1 A B 0, ← Category.assoc, e0, H.lift_fst]
    exact t.condition 0
  · intro t i
    fin_cases i
    · exact H.lift_fst _ _ _
    · exact H.lift_snd _ _ _
  · intro t m _ hm
    apply H.hom_ext
    · rw [H.lift_fst, ← hm 0]; rfl
    · rw [H.lift_snd, ← hm 1]; rfl

end GlobalTheory.CechOne
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitWidePullbackConeSpecTensorSquareStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

theorem _root_.GlobalTheory.T.isLimit_widePullbackCone_spec_tensorSquare : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (1 + 1) => GlobalTheory.CechOne.fB A B) (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B)))) (GlobalTheory.CechOne.y1 A B) (GlobalTheory.CechOne.hy1 A B))) := by
  first | (exact @GlobalTheory.CechOne.isLimit_widePullback_tensor) | (exact GlobalTheory.CechOne.isLimit_widePullback_tensor) | (intros; apply GlobalTheory.CechOne.isLimit_widePullback_tensor  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCocycleCoboundaryIff

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

noncomputable section

namespace GlobalTheory.CechOne

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem isCls_zero (R : Type) [CommRing R] (F : Shv R) (E : Spc) :
    IsCls (0 : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F) (0 : H R E F ((1 : ℕ) : ℤ)) := by
  have hc0 : ∀ {n : ℕ}, cobd (0 : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) = 0 := by
    intro n; simp [cobd]
  obtain ⟨x, hx⟩ := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F E 1).1 0 hc0
  have h4 := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F E 0).2.2.2.1 0 x (by rw [hc0]; exact hx)
  rw [h4] at hx
  exact hx

theorem mul_inv_mul_cancel_comm {M : Type*} [AddCommGroup M] {a b c : M} (h : a - b + c = 0) : b = c + a := by
  rw [sub_add_eq_add_sub, sub_eq_zero] at h
  rw [← h, add_comm]

theorem sub_add_eq_zero_of_eq_add {M : Type*} [AddCommGroup M] {a b c : M} (h : b = c + a) : a - b + c = 0 := by
  rw [h]
  abel

theorem mem_Z1_iff_cocycle (R : Type) [CommRing R] (F : Shv R) (w : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) :
    w ∈ Z1 F A B ↔
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom w =
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom w +
      ((onRings F).map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom)).hom w := Iff.rfl

theorem cobd_eq_zero_iff (R : Type) [CommRing R] (F : Shv R) (s : (free R).obj ((cech (fB A B)).obj (op ⦋1⦌)) ⟶ F) :
    cobd s = 0 ↔
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom (val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B)) =
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom (val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B)) +
      ((onRings F).map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom)).hom (val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B)) := by
  have hinj := (GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 2 _ _ (y2 A B) (hy2 A B) (GlobalTheory.T.triple_tensor_wide_pullback_limit A B).some).1
  constructor
  · intro h
    have h2 := (val_coboundary_second_level A B R F s).symm.trans
      ((congrArg (fun t => val t (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))) (P2 A B)) h).trans (val_zero R _ _))
    exact mul_inv_mul_cancel_comm h2
  · intro h
    apply hinj
    change val (cobd s) (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))) (P2 A B) = val 0 (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))) (P2 A B)
    rw [val_zero]
    exact (val_coboundary_second_level A B R F s).trans (sub_add_eq_zero_of_eq_add h)

def Rel (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B) (x : H R (sp A) F 1) : Prop :=
  ∃ s : (free R).obj ((cech (fB A B)).obj (op ⦋1⦌)) ⟶ F,
    val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B) = (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) ∧
      IsCls s (pull R (cechAug (fB A B)) F ((1 : ℕ) : ℤ) x)

theorem rel_unique [Algebra.Etale A B] [Module.FaithfullyFlat A B] (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B)
    (x x' : H R (sp A) F 1) (h : Rel A B R F u x) (h' : Rel A B R F u x') : x = x' := by
  obtain ⟨s, hs, hx⟩ := h
  obtain ⟨s', hs', hx'⟩ := h'
  have hss : s = s' :=
    (GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 1 _ _ (y1 A B) (hy1 A B) (GlobalTheory.T.isLimit_widePullbackCone_spec_tensorSquare A B).some).1 (hs.trans hs'.symm)
  subst hss
  have := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F (cech (fB A B)) 1).2.2.1 s _ _ hx hx'
  obtain ⟨h1, h2⟩ := smooth_surj A B
  exact (GlobalTheory.T.etC_a2 R (fB A B) F ((1 : ℕ) : ℤ)).1 this

theorem rel_exists [Algebra.Etale A B] [Module.FaithfullyFlat A B] (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B) :
    ∃ x, Rel A B R F u x := by
  obtain ⟨s, hs⟩ := (GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 1 _ _ (y1 A B) (hy1 A B) (GlobalTheory.T.isLimit_widePullbackCone_spec_tensorSquare A B).some).2
    (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B)))
  have hs' : val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B) = (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) := hs
  have hc : cobd s = 0 := (cobd_eq_zero_iff A B R F s).2 (by rw [hs']; exact (mem_Z1_iff_cocycle A B R F _).1 u.2)
  obtain ⟨y, hy⟩ := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F (cech (fB A B)) 1).1 s hc
  obtain ⟨h1, h2⟩ := smooth_surj A B
  obtain ⟨x, hx⟩ := (GlobalTheory.T.etC_a2 R (fB A B) F ((1 : ℕ) : ℤ)).2 y
  exact ⟨x, s, hs', hx ▸ hy⟩

variable {A B} in
theorem rel_add (R : Type) [CommRing R] (F : Shv R) (u u' : Z1 F A B) (x x' : H R (sp A) F 1)
    (h : Rel A B R F u x) (h' : Rel A B R F u' x') : Rel A B R F (u + u') (x + x') := by
  obtain ⟨s, hs, hx⟩ := h
  obtain ⟨s', hs', hx'⟩ := h'
  refine ⟨s + s', ?_, ?_⟩
  · rw [val_add, hs, hs']
    rfl
  · rw [map_add (f := _)]
    exact (GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 1).2.1 s s' _ _ hx hx'

theorem rel_zero (R : Type) [CommRing R] (F : Shv R) : Rel A B R F 0 0 := by
  refine ⟨0, ?_, ?_⟩
  · rw [val_zero]
    rfl
  · rw [map_zero]
    exact isCls_zero R F _


open Classical in
def gam (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B) : H R (sp A) F 1 :=
  if Algebra.Etale A B ∧ Module.FaithfullyFlat A B then Classical.epsilon (Rel A B R F u) else 0

theorem gam_spec [Algebra.Etale A B] [Module.FaithfullyFlat A B] (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B) :
    Rel A B R F u (gam A B R F u) := by
  unfold gam
  rw [if_pos ⟨inferInstance, inferInstance⟩]
  exact Classical.epsilon_spec (rel_exists A B R F u)

theorem gam_eq [Algebra.Etale A B] [Module.FaithfullyFlat A B] (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B)
    (x : H R (sp A) F 1) : gam A B R F u = x ↔ Rel A B R F u x :=
  ⟨fun h => h ▸ gam_spec A B R F u, fun h => rel_unique A B R F u _ _ (gam_spec A B R F u) h⟩

def gamHom (R : Type) [CommRing R] (F : Shv R) : Z1 F A B →+ H R (sp A) F 1 where
  toFun := gam A B R F
  map_zero' := by
    by_cases h : Algebra.Etale A B ∧ Module.FaithfullyFlat A B
    · haveI := h.1
      haveI := h.2
      exact (gam_eq A B R F 0 0).2 (rel_zero A B R F)
    · unfold gam
      rw [if_neg h]
  map_add' u u' := by
    by_cases h : Algebra.Etale A B ∧ Module.FaithfullyFlat A B
    · haveI := h.1
      haveI := h.2
      exact (gam_eq A B R F _ _).2 (rel_add R F _ _ _ _ (gam_spec A B R F u) (gam_spec A B R F u'))
    · unfold gam
      rw [if_neg h, if_neg h, if_neg h, add_zero]

theorem cech1 : ∀ (R : Type) [CommRing R] (F : Shv R) (A : Type) [CommRing A], ∃ γ : ∀ (B : Type) [CommRing B] [Algebra A B], Z1 F A B →+ H R (sp A) F 1, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.FaithfullyFlat A B], (∀ u : Z1 F A B, γ B u = 0 ↔ ∃ v : (onRings F).obj (CommRingCat.of B), (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) = ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)).hom v - ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom)).hom v) ∧ (∀ x : H R (sp A) F 1, pull R (spMap (algebraMap A B)) F 1 x = 0 → ∃ u, γ B u = x) ∧ (∀ u, pull R (spMap (algebraMap A B)) F 1 (γ B u) = 0) ∧ ∀ (B' : Type) [CommRing B'] [Algebra A B'] [Algebra.Etale A B'] [Module.FaithfullyFlat A B'] (φ : B →ₐ[A] B') (u : Z1 F A B) (u' : Z1 F A B'), (u' : (onRings F).obj (CommRingCat.of (B' ⊗[A] B'))) = ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map φ φ).toRingHom)).hom u → γ B' u' = γ B u := by
  intro R _ F A _
  refine ⟨fun B => gamHom A B R F, ?_⟩
  intro B _ _ _ _
  have bij0 := GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 0 _ _ _ _ (GlobalTheory.T.isLimit_widePullbackCone_spec_single A B).some
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    change gam A B R F u = 0 ↔ _
    rw [gam_eq]
    constructor
    · rintro ⟨s, hs, hx⟩
      rw [map_zero] at hx
      obtain ⟨t, rfl⟩ := GlobalTheory.T.simplicialCochain_coboundary_of_class_zero R F _ s hx
      exact ⟨val t (Spec (CommRingCat.of B)) (P0 A B), by rw [← hs, val_coboundary_first_level]⟩
    · rintro ⟨v, hv⟩
      obtain ⟨t, ht⟩ := bij0.2 v
      have ht' : val t (Spec (CommRingCat.of B)) (P0 A B) = v := ht
      have hval : val (cobd t) (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B) = (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) := by
        rw [val_coboundary_first_level, ht', hv]
      have hc : cobd (cobd t) = 0 := (cobd_eq_zero_iff A B R F _).2 (by rw [hval]; exact (mem_Z1_iff_cocycle A B R F _).1 u.2)
      refine ⟨cobd t, hval, ?_⟩
      rw [map_zero]
      obtain ⟨x, hx⟩ := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 1).1 (cobd t) hc
      have h4 := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 0).2.2.2.1 t x hx
      rw [h4] at hx
      exact hx
  · intro x hx
    obtain ⟨s, hs, hcls⟩ := GlobalTheory.T.etaleCohomology_one_cechCocycle_of_pullback_zero R F _ _ (fB A B) x hx
    exact ⟨⟨val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B), (mem_Z1_iff_cocycle A B R F _).2 ((cobd_eq_zero_iff A B R F s).1 hs)⟩, (gam_eq A B R F _ x).2 ⟨s, rfl, hcls⟩⟩
  · intro u
    obtain ⟨s, hs, hcls⟩ := gam_spec A B R F u
    exact GlobalTheory.T.etaleCohomologyPullback_eq_zero_of_cechOneCocycle R F (fB A B) s ((cobd_eq_zero_iff A B R F s).2 (by rw [hs]; exact (mem_Z1_iff_cocycle A B R F _).1 u.2)) _ hcls
  · intro B' _ _ _ _ φ u u' hu
    change gam A B' R F u' = gam A B R F u
    rw [gam_eq]
    obtain ⟨s, hs, hcls⟩ := gam_spec A B R F u
    refine ⟨(free R).map ((cechMap (fB A B) (fB A B') _ (spec_algHom φ)).app (op ⦋1⦌)) ≫ s, ?_, ?_⟩
    · rw [val_cech_map_first_level, hs, hu]
    · have := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 1).2.2.2.2 _ (cechMap (fB A B) (fB A B') _ (spec_algHom φ)) s _ hcls
      rw [← pull_comp, cechMap_aug] at this
      exact this

end GlobalTheory.CechOne
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCocycleCoboundaryIffStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etale_cocycle_coboundary_iff : ∀ (R : Type) [CommRing R] (F : Shv R) (A : Type) [CommRing A], ∃ γ : ∀ (B : Type) [CommRing B] [Algebra A B], Z1 F A B →+ H R (sp A) F 1, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.FaithfullyFlat A B], (∀ u : Z1 F A B, γ B u = 0 ↔ ∃ v : (onRings F).obj (CommRingCat.of B), (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) = ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)).hom v - ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom)).hom v) ∧ (∀ x : H R (sp A) F 1, pull R (spMap (algebraMap A B)) F 1 x = 0 → ∃ u, γ B u = x) ∧ (∀ u, pull R (spMap (algebraMap A B)) F 1 (γ B u) = 0) ∧ ∀ (B' : Type) [CommRing B'] [Algebra A B'] [Algebra.Etale A B'] [Module.FaithfullyFlat A B'] (φ : B →ₐ[A] B') (u : Z1 F A B) (u' : Z1 F A B'), (u' : (onRings F).obj (CommRingCat.of (B' ⊗[A] B'))) = ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map φ φ).toRingHom)).hom u → γ B' u' = γ B u := by
  first | (exact @GlobalTheory.CechOne.cech1) | (exact GlobalTheory.CechOne.cech1) | (intros; apply GlobalTheory.CechOne.cech1  <;> assumption)
end
end
