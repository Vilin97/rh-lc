module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelSpecTensorPowerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraStrictlyHenselianInductionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentKummerCupProductBijectiveStrictlyHenseliaStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.LinearAlgebra.PiTensorProduct.Finite

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentKummerCupProductMapBijectiveFiniteStrictH

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section
namespace GlobalTheory.EtC.LaurentMapPullbackBijective

theorem laurentMap_coeff {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (p : LaurentPolynomial A) (n : ℤ) :
    (laurentMap f p).coeff n = f (p.coeff n) := by
  unfold laurentMap
  simp

theorem laurentMap_id (A : Type) [CommRing A] : laurentMap (RingHom.id A) = RingHom.id _ :=
  AddMonoidAlgebra.mapRingHom_id

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (sp A) := by
  simp [spMap]

theorem pull_bijective_of_inverse (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : B →+* A)
    (hgf : g.comp f = RingHom.id A) (hfg : f.comp g = RingHom.id B) (n i : ℤ) :
    Function.Bijective (pull _ (spMap f) (tw q i) n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull _ (spMap g) (tw q i) n, fun x => ?_, fun y => ?_⟩
  · rw [← GmPhiNat.pull_spMap_comp, hgf, spMap_id, pull_id]
  · rw [← GmPhiNat.pull_spMap_comp, hfg, spMap_id, pull_id]

theorem ht_subsingleton (q : ℕ) (T : Type) [CommRing T] [Subsingleton T] (n i : ℤ) :
    Subsingleton (Ht q (sp T) n i) := by
  have hb := GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q T T n i
  have hfs : RingHom.fst T T = RingHom.snd T T := RingHom.ext fun _ => Subsingleton.elim _ _
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, hx⟩ := hb.2 (a, b)
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only at h1 h2
  rw [hfs] at h1
  exact h1.symm.trans h2

theorem laurent_subsingleton (T : Type) [CommRing T] [Subsingleton T] : Subsingleton (LaurentPolynomial T) := by
  refine subsingleton_of_zero_eq_one ?_
  rw [← map_zero (LaurentPolynomial.C : T →+* LaurentPolynomial T), ← map_one (LaurentPolynomial.C : T →+* LaurentPolynomial T),
    Subsingleton.elim (0 : T) 1]

theorem gmPhi_bijective_of_subsingleton (q : ℕ) (T : Type) [CommRing T] [Subsingleton T] (i : ℤ) :
    Function.Bijective (gmPhi q T i) := by
  haveI := ht_subsingleton q T 0 (i - 1)
  haveI := laurent_subsingleton T
  haveI := ht_subsingleton q (LaurentPolynomial T) 1 i
  exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

theorem gmPhi_bijective_of_equiv (h6 : DivisorNaturality) (q : ℕ) [NeZero q] {T T' : Type} [CommRing T] [CommRing T']
    (e : T ≃+* T') (hq : IsUnit (q : T)) (i : ℤ) (h : Function.Bijective (gmPhi q T i)) :
    Function.Bijective (gmPhi q T' i) := by
  have hcomm : (gmPhi q T' i) ∘ (pull _ (spMap (e : T →+* T')) _ 0) =
      (pull _ (spMap (laurentMap (e : T →+* T'))) _ 1) ∘ (gmPhi q T i) :=
    funext fun a => (gmPhi_nat h6 q (e : T →+* T') hq i a).symm
  have hgf : (e.symm : T' →+* T).comp (e : T →+* T') = RingHom.id T := by ext; simp
  have hfg : (e : T →+* T').comp (e.symm : T' →+* T) = RingHom.id T' := by ext; simp
  have hpull := pull_bijective_of_inverse q (e : T →+* T') (e.symm : T' →+* T) hgf hfg 0 (i - 1)
  have hpullL := pull_bijective_of_inverse q (laurentMap (e : T →+* T')) (laurentMap (e.symm : T' →+* T))
    (by rw [← GmPhiNat.laurentMap_comp, hgf, laurentMap_id])
    (by rw [← GmPhiNat.laurentMap_comp, hfg, laurentMap_id]) 1 i
  rw [← Function.Bijective.of_comp_iff _ hpull, hcomm]
  exact hpullL.comp h

theorem laurentProd_bijective (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] :
    Function.Bijective ((laurentMap (RingHom.fst T₁ T₂)).prod (laurentMap (RingHom.snd T₁ T₂))) := by
  constructor
  · intro p p' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [RingHom.prod_apply] at h1 h2
    apply AddMonoidAlgebra.ext
    refine Finsupp.ext fun n => ?_
    have e1 := congrArg (fun r => r.coeff n) h1
    have e2 := congrArg (fun r => r.coeff n) h2
    simp only [laurentMap_coeff, RingHom.coe_fst, RingHom.coe_snd] at e1 e2
    exact Prod.ext e1 e2
  · rintro ⟨p₁, p₂⟩
    refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.zipWith Prod.mk (by simp) p₁.coeff p₂.coeff), ?_⟩
    simp only [RingHom.prod_apply]
    refine Prod.ext (AddMonoidAlgebra.ext ?_) (AddMonoidAlgebra.ext ?_)
    · ext n; simp [laurentMap_coeff]
    · ext n; simp [laurentMap_coeff]

theorem gmPhi_bijective_prod (h6 : DivisorNaturality) (q : ℕ) [NeZero q] (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂]
    (hq : IsUnit (q : T₁ × T₂)) (i : ℤ) (h₁ : Function.Bijective (gmPhi q T₁ i))
    (h₂ : Function.Bijective (gmPhi q T₂ i)) : Function.Bijective (gmPhi q (T₁ × T₂) i) := by
  set f₁ := RingHom.fst T₁ T₂
  set f₂ := RingHom.snd T₁ T₂
  set ψ := (laurentMap f₁).prod (laurentMap f₂)
  have hα := GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q T₁ T₂ 0 (i - 1)
  have hγ := GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q (LaurentPolynomial T₁) (LaurentPolynomial T₂) 1 i
  have hψ : Function.Bijective ψ := laurentProd_bijective T₁ T₂
  let e := RingEquiv.ofBijective ψ hψ
  have hgf : e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := RingHom.ext fun x => e.symm_apply_apply x
  have hfg : e.toRingHom.comp e.symm.toRingHom = RingHom.id _ := RingHom.ext fun x => e.apply_symm_apply x
  have hψpull := pull_bijective_of_inverse q e.toRingHom e.symm.toRingHom hgf hfg 1 i
  have he : e.toRingHom = ψ := rfl
  have hl₁ : laurentMap f₁ = (RingHom.fst _ _).comp ψ := rfl
  have hl₂ : laurentMap f₂ = (RingHom.snd _ _).comp ψ := rfl
  let β := fun y : Ht q (sp (LaurentPolynomial (T₁ × T₂))) 1 i =>
    (pull _ (spMap (laurentMap f₁)) _ 1 y, pull _ (spMap (laurentMap f₂)) _ 1 y)
  have hβ : Function.Bijective β := by
    have : β = (fun x : Ht q (sp (LaurentPolynomial T₁ × LaurentPolynomial T₂)) 1 i =>
        (pull _ (spMap (RingHom.fst (LaurentPolynomial T₁) (LaurentPolynomial T₂))) _ 1 x,
          pull _ (spMap (RingHom.snd (LaurentPolynomial T₁) (LaurentPolynomial T₂))) _ 1 x)) ∘
        (pull _ (spMap ψ) _ 1) := by
      funext y
      simp only [β, Function.comp_apply, hl₁, hl₂, GmPhiNat.pull_spMap_comp]
    rw [this]
    rw [he] at hψpull
    exact hγ.comp hψpull
  have hu₁ : IsUnit (q : T₁) := by simpa using hq.map f₁
  have hu₂ : IsUnit (q : T₂) := by simpa using hq.map f₂
  have hcomm : β ∘ (gmPhi q (T₁ × T₂) i) =
      (Prod.map (gmPhi q T₁ i) (gmPhi q T₂ i)) ∘
        (fun x : Ht q (sp (T₁ × T₂)) 0 (i - 1) => (pull _ (spMap f₁) _ 0 x, pull _ (spMap f₂) _ 0 x)) := by
    funext a
    simp only [β, Function.comp_apply, Prod.map_apply]
    rw [gmPhi_nat h6 q f₁ hq i a, gmPhi_nat h6 q f₂ hq i a]
  rw [← Function.Bijective.of_comp_iff' hβ, hcomm]
  exact (h₁.prodMap h₂).comp hα

end GlobalTheory.EtC.LaurentMapPullbackBijective


open GlobalTheory.EtC.LaurentMapPullbackBijective in
theorem GlobalTheory.EtC.GmStep.gmPhi_bijective_finite : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → ∀ i : ℤ, Function.Bijective (gmPhi q T i) := by
  intro q _ A _ hA hq T _ _ hT
  have h6 : DivisorNaturality := GlobalTheory.T.cup_chern_kummer_pullback_naturality
  have hunit : ∀ (S : Type) [CommRing S] [Algebra A S], IsUnit (q : S) := fun S _ _ => by
    simpa using hq.map (algebraMap A S)
  exact GlobalTheory.T.finiteAlgebra_strictlyHenselian_induction A hA (fun S _ _ => ∀ i : ℤ, Function.Bijective (gmPhi q S i))
    (fun S S' _ _ _ _ e h i => gmPhi_bijective_of_equiv h6 q e.toRingEquiv (hunit S) i (h i))
    (fun S _ _ _ i => gmPhi_bijective_of_subsingleton q S i)
    (fun S₁ S₂ _ _ _ _ _ _ h₁ h₂ i => gmPhi_bijective_prod h6 q S₁ S₂ (hunit (S₁ × S₂)) i (h₁ i) (h₂ i))
    (fun S _ _ _ hS i => GlobalTheory.T.laurentKummerCupProduct_bijective_strictlyHenselian q S hS (hunit S) i)
    T hT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentKummerCupProductMapBijectiveFiniteStrictHStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.laurentKummerCupProductMap_bijective_finite_strictHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ i : ℤ, Function.Bijective (gmPhi q T i) := by
  first | (exact @GlobalTheory.EtC.GmStep.gmPhi_bijective_finite) | (exact GlobalTheory.EtC.GmStep.gmPhi_bijective_finite) | (intros; apply GlobalTheory.EtC.GmStep.gmPhi_bijective_finite  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEqOfCodimOneEq

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep.LevelOne

variable {R : Type} [CommRing R]

theorem pull_iso_bijective' {E E' : Spc} (e : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast (q := q) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem laurentVar_map {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) :
    Units.map (Spec.map (CommRingCat.ofHom (laurentMap f))).appTop.hom.toMonoidHom (laurentVar B) = laurentVar C := by
  ext
  simp only [laurentVar, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  have h := congrArg (fun g => g.hom (LaurentPolynomial.T 1 : LaurentPolynomial B))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (laurentMap f)))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h
  rw [laurentMap_T] at h
  exact h.symm

end GlobalTheory.EtC.GmStep.LevelOne

namespace GlobalTheory.EtC.GmStep.LevelOne

theorem rowOne_bijective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (A' : Type) [CommRing A'] [Algebra A A'], Module.Finite A A' → ∀ (k : ℕ) (i : ℤ),
    Function.Bijective (rowOne A A' q i k) := by
  intro q _ A _ hA hq A' _ _ hfin k i
  obtain ⟨e0, e, h1, h2⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  haveI := hfin
  have hT : Module.Finite A (PiTensorProduct A (fun _ : Fin (k + 1) => A')) := inferInstance
  have hr1 := GlobalTheory.T.laurentKummerCupProductMap_bijective_finite_strictHenselian q A hA hq (PiTensorProduct A (fun _ : Fin (k + 1) => A')) hT i
  have hmap1 := congrArg (fun f => disc.map f) h1
  have hmap2 := congrArg (fun f => disc.map f) h2
  simp only [Functor.map_comp] at hmap1 hmap2
  have hqL : IsUnit (q : Γ(Spec (CommRingCat.of (LaurentPolynomial A)), ⊤)) := by
    have := hq.map ((Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv.hom.comp
      (LaurentPolynomial.C : A →+* LaurentPolynomial A))
    simpa using this
  have hkum : pull _ (disc.map e.hom) (tw q 1) 1 (pull _ (augK A A' k) (tw q 1) 1 (kum q (laurentVar A))) =
      kum q (laurentVar (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) := by
    rw [← pull_comp, augK]
    erw [hmap2]
    have := (GlobalTheory.EtC.a6nat_holds q).2.2.2 (Spec.map (CommRingCat.ofHom (laurentMap (algebraMap A
      (PiTensorProduct A (fun _ : Fin (k + 1) => A')))))) (laurentVar A) hqL
    rw [laurentVar_map] at this
    exact this
  have hcst : ∀ a, pull _ (disc.map e.hom) (tw q (i - 1)) 0
      (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q (i - 1)) 0 a) =
      pull _ (spMap (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) (tw q (i - 1)) 0
        (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0 a) := by
    intro a
    rw [← pull_comp, hmap1, pull_comp]
    rfl
  have heq : ∀ a, pull _ (disc.map e.hom : sp (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) ⟶ _) (tw q i) 1 (rowOne A A' q i k a) =
      gmPhi q (PiTensorProduct A (fun _ : Fin (k + 1) => A')) i (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0 a) := by
    intro a
    simp only [rowOne, gmPhi, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [pull_cast, (GlobalTheory.EtC.a6nat_holds q).1, hcst, hkum]
    rfl
  have hcomp : (pull _ (disc.map e.hom : sp (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) ⟶ _) (tw q i) 1) ∘ (rowOne A A' q i k) =
      (gmPhi q (PiTensorProduct A (fun _ : Fin (k + 1) => A')) i) ∘ (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0) :=
    funext heq
  have he : Function.Bijective (pull _ (disc.map e.hom : sp (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) ⟶ _) (tw q i) 1) :=
    pull_iso_bijective' (disc.mapIso e) (tw q i) 1
  have he0 : Function.Bijective (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0) :=
    pull_iso_bijective' (disc.mapIso e0) (tw q (i - 1)) 0
  rw [← Function.Bijective.of_comp_iff' he, hcomp]
  exact hr1.comp he0

end GlobalTheory.EtC.GmStep.LevelOne
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDegreeZeroBijective

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.cech_degree_zero_bijective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (i : ℤ), Function.Bijective (rowOne A A' q i k) := by
  first | (exact @GlobalTheory.EtC.GmStep.LevelOne.rowOne_bijective) | (exact GlobalTheory.EtC.GmStep.LevelOne.rowOne_bijective) | (intros; apply GlobalTheory.EtC.GmStep.LevelOne.rowOne_bijective  <;> assumption)
end
end
