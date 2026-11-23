module

public import Development.EtaleCohomology.CohomologicalPurity.LeafRootPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc
public import Development.EtaleCohomology.CohomologicalPurity.LeafHensCutDef
public import Development.EtaleCohomology.CohomologicalPurity.LeafColHensPf
import Mathlib.Tactic.Linter.Style
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
public import Development.EtaleCohomology.CohomologicalPurity.LeafInvPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafRootStdPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafStagePf
public import Development.EtaleCohomology.CohomologicalPurity.LeafSupPf

-- Source module: Development.EtaleCohomology.CohomologicalPurity.LeafCoeqPf

section

@[expose] public section

noncomputable section
open scoped TensorProduct

namespace LateralTheory.CohomologicalPurity.Hz

theorem coeq_elem {A S S' : Type} [CommRing A] [CommRing S] [CommRing S'] (φ : A →+* S) (φ' : A →+* S')
    (I : Ideal A) (u v : S →+* S') (hφ : Good φ I) (hu : u.comp φ = φ') (hv : v.comp φ = φ') :
    ∃ e : S', (∀ s, (v s - u s) * e = 0) ∧ e - 1 ∈ I.map φ' := by
  let := φ.toAlgebra
  let := φ'.toAlgebra
  have : Algebra.Etale A S := hφ.etale
  let u' : S →ₐ[A] S' := { u with commutes' := fun a => RingHom.congr_fun hu a }
  let v' : S →ₐ[A] S' := { v with commutes' := fun a => RingHom.congr_fun hv a }
  obtain ⟨t, ht1, ht2⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := S)).1 inferInstance
  refine ⟨Algebra.TensorProduct.productMap u' v' t, fun s => ?_, ?_⟩
  · have h := congrArg (Algebra.TensorProduct.productMap u' v') (ht1 s)
    simpa [map_mul, map_sub, Algebra.TensorProduct.productMap_apply_tmul, u', v'] using h
  · have hmem : ∀ x ∈ I.map φ, u x ∈ I.map φ' ∧ v x ∈ I.map φ' := fun x hx => by
      refine ⟨?_, ?_⟩
      · have := Ideal.mem_map_of_mem u hx
        rwa [Ideal.map_map, hu] at this
      · have := Ideal.mem_map_of_mem v hx
        rwa [Ideal.map_map, hv] at this
    let q := Ideal.Quotient.mkₐ A (I.map φ')
    have hqv : q.comp v' = q.comp u' := by
      ext s
      obtain ⟨a, ha⟩ := hφ.surj s
      have e1 : v s - u s = v (s - φ a) - u (s - φ a) := by
        have h1 : v (φ a) = u (φ a) := (RingHom.congr_fun hv a).trans (RingHom.congr_fun hu a).symm
        rw [map_sub, map_sub, h1]; ring
      change Ideal.Quotient.mk _ (v s) = Ideal.Quotient.mk _ (u s)
      rw [Ideal.Quotient.eq, e1]
      exact Ideal.sub_mem _ (hmem _ ha).2 (hmem _ ha).1
    have hprod : q.comp (Algebra.TensorProduct.productMap u' v') = q.comp (u'.comp (Algebra.TensorProduct.lmul' A)) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      have hb := AlgHom.congr_fun hqv b
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.productMap_apply_tmul, map_mul,
        Algebra.TensorProduct.lmul'_apply_tmul] at hb ⊢
      rw [hb]
    have h := AlgHom.congr_fun hprod t
    simp only [AlgHom.comp_apply] at h
    rw [ht2, map_one] at h
    rw [← Ideal.Quotient.eq]
    simpa [q] using h

theorem LeafCoeq_of (hInv : LeafInv) (hComp : LeafComp) : LeafCoeq := by
  intro A S S' _ _ _ φ φ' I u v hφ hφ' hu hv
  obtain ⟨e, he1, he2⟩ := coeq_elem φ φ' I u v hφ hu hv
  obtain ⟨T, _, ψ, hg, hunit⟩ := hInv S' (I.map φ') (e - 1) he2
  rw [add_sub_cancel] at hunit
  refine ⟨T, inferInstance, ψ, RingHom.ext fun s => ?_, hComp.2 A S' T φ' ψ I hφ' hg⟩
  have h := congrArg ψ (he1 s)
  rw [map_mul, map_zero, hunit.mul_left_eq_zero, map_sub, sub_eq_zero] at h
  exact h.symm

end LateralTheory.CohomologicalPurity.Hz
end
end
end

-- Source module: Development.EtaleCohomology.CohomologicalPurity.LeafColUnivPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Hz

theorem LeafColUniv_of : LeafColUniv := by
  intro A _ I Δ c hc η hη B _ J hJ ψ hψ
  have hu : ∀ j, ∃! χ : Δ.D.obj j →+* B, χ.comp (Δ.s j) = ψ := fun j => (Δ.good j).univ B J hJ ψ hψ
  choose χ hχ hχu using hu
  have hnat : ∀ {j k : Δ.J} (e : j ⟶ k), (χ k).comp (Δ.D.map e).hom = χ j := fun {j k} e => by
    apply hχu j
    rw [RingHom.comp_assoc, Δ.nat e, hχ k]
  let cB : Cocone Δ.D := ⟨CommRingCat.of B, ⟨fun j => CommRingCat.ofHom (χ j), fun j k e => by
    apply CommRingCat.hom_ext
    simpa using hnat e⟩⟩
  let d := hc.desc cB
  have hfac : ∀ j, d.hom.comp (Δ.leg c j) = χ j := fun j => by
    have := hc.fac cB j
    exact congrArg CommRingCat.Hom.hom this
  obtain ⟨j₀⟩ : Nonempty Δ.J := IsFiltered.nonempty
  refine ⟨d.hom, ?_, fun χ' h' => ?_⟩
  · show d.hom.comp η = ψ
    rw [← hη j₀, ← RingHom.comp_assoc, hfac, hχ]
  · have h2 : ∀ j, χ'.comp (Δ.leg c j) = χ j := fun j => by
      apply hχu j
      rw [RingHom.comp_assoc, hη j, h']
    have : CommRingCat.ofHom χ' = d := hc.hom_ext fun j => by
      apply CommRingCat.hom_ext
      change χ'.comp (Δ.leg c j) = d.hom.comp (Δ.leg c j)
      rw [h2, hfac]
    rw [← this]
    rfl

end LateralTheory.CohomologicalPurity.Hz
end
end
end

-- Source module: Development.EtaleCohomology.CohomologicalPurity.LeafCompPf

section

@[expose] public section

noncomputable section

namespace LateralTheory.CohomologicalPurity.Hz

theorem good_iso (A S : Type) [CommRing A] [CommRing S] (e : A ≃+* S) (I : Ideal A) : Good (e : A →+* S) I := by
  refine ⟨RingHom.Etale.of_bijective e.bijective, ⟨(Ideal.Quotient.mk I).comp (e.symm : S →+* A), ?_⟩, fun s => ⟨e.symm s, ?_⟩, ?_⟩
  · ext a; simp
  · simp
  · intro B _ J _ ψ _
    refine ⟨ψ.comp (e.symm : S →+* A), ?_, fun χ hχ => ?_⟩
    · ext a; simp
    · ext s
      have := congrArg (fun f : A →+* B => f (e.symm s)) hχ
      simpa using this

theorem good_comp (A S T : Type) [CommRing A] [CommRing S] [CommRing T] (φ : A →+* S) (ψ : S →+* T) (I : Ideal A)
    (h1 : Good φ I) (h2 : Good ψ (I.map φ)) : Good (ψ.comp φ) I := by
  obtain ⟨r1, hr1⟩ := h1.retr
  obtain ⟨r2, hr2⟩ := h2.retr
  have hk : I.map φ ≤ RingHom.ker r1 := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change (r1.comp φ) a = 0
    rw [hr1]
    exact Ideal.Quotient.eq_zero_iff_mem.2 ha
  refine ⟨RingHom.Etale.stableUnderComposition φ ψ h1.etale h2.etale,
    ⟨(Ideal.Quotient.lift (I.map φ) r1 (fun a ha => hk ha)).comp r2, ?_⟩, fun t => ?_, ?_⟩
  · ext a
    have e2 : r2 (ψ (φ a)) = Ideal.Quotient.mk (I.map φ) (φ a) := congrArg (fun f : S →+* S ⧸ I.map φ => f (φ a)) hr2
    simp only [RingHom.comp_apply, e2, Ideal.Quotient.lift_mk]
    exact congrArg (fun f : A →+* A ⧸ I => f a) hr1
  · obtain ⟨s, hs⟩ := h2.surj t
    obtain ⟨a, ha⟩ := h1.surj s
    refine ⟨a, ?_⟩
    rw [Ideal.map_map] at hs
    have h3 : ψ (s - φ a) ∈ (I.map φ).map ψ := Ideal.mem_map_of_mem ψ ha
    rw [Ideal.map_map] at h3
    have : t - (ψ.comp φ) a = (t - ψ s) + ψ (s - φ a) := by simp [map_sub]
    rw [this]
    exact Ideal.add_mem _ hs h3
  · intro B _ J hB χ0 hI
    obtain ⟨χ1, hχ1, hu1⟩ := h1.univ B J hB χ0 hI
    have hI2 : I.map φ ≤ J.comap χ1 := by
      rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hχ1]
      exact hI
    obtain ⟨χ2, hχ2, hu2⟩ := h2.univ B J hB χ1 hI2
    refine ⟨χ2, ?_, fun χ hχ => ?_⟩
    · show χ2.comp (ψ.comp φ) = χ0
      rw [← RingHom.comp_assoc, hχ2, hχ1]
    · apply hu2
      apply hu1
      show (χ.comp ψ).comp φ = χ0
      rw [RingHom.comp_assoc]
      exact hχ

theorem LeafComp_of : LeafComp := ⟨good_iso, good_comp⟩

end LateralTheory.CohomologicalPurity.Hz
end
end
end

-- Source module: Development.EtaleCohomology.CohomologicalPurity.LeafDiagPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Hz.DiagPf

variable {A : Type} [CommRing A] (I : Ideal A)

structure Obj where
  n : ℕ
  K : Ideal (MvPolynomial (Fin n) A)
  good : Good (algebraMap A (MvPolynomial (Fin n) A ⧸ K)) I

variable {I}

abbrev Obj.Q (X : Obj I) : Type := MvPolynomial (Fin X.n) A ⧸ X.K

abbrev Obj.s (X : Obj I) : A →+* X.Q := algebraMap A X.Q

instance : SmallCategory (Obj I) where
  Hom X Y := {f : X.Q →+* Y.Q // f.comp X.s = Y.s}
  id X := ⟨RingHom.id _, RingHom.id_comp _⟩
  comp f g := ⟨g.1.comp f.1, by rw [RingHom.comp_assoc, f.2, g.2]⟩
  id_comp f := Subtype.ext (RingHom.comp_id _)
  comp_id f := Subtype.ext (RingHom.id_comp _)
  assoc f g h := Subtype.ext (RingHom.comp_assoc _ _ _).symm

def DF : Obj I ⥤ CommRingCat.{0} where
  obj X := CommRingCat.of X.Q
  map f := CommRingCat.ofHom f.1
  map_id _ := rfl
  map_comp _ _ := rfl

theorem key (hC : LeafComp) {T : Type} [CommRing T] (φ : A →+* T) (h : Good φ I) :
    ∃ (X : Obj I) (ρ : T →+* X.Q), ρ.comp φ = X.s := by
  let _ := φ.toAlgebra
  have : Algebra.Etale A T := h.etale
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType A T)
  let e0 := Ideal.quotientKerAlgEquivOfSurjective hf
  have hcomp : (e0.symm : T →+* MvPolynomial (Fin n) A ⧸ RingHom.ker f).comp φ =
      algebraMap A (MvPolynomial (Fin n) A ⧸ RingHom.ker f) := by
    have := AlgHom.comp_algebraMap (e0.symm : T →ₐ[A] MvPolynomial (Fin n) A ⧸ RingHom.ker f)
    rw [← RingHom.algebraMap_toAlgebra φ]
    exact this
  have hg : Good (algebraMap A (MvPolynomial (Fin n) A ⧸ RingHom.ker f)) I := by
    rw [← hcomp]
    exact hC.2 _ _ _ _ _ _ h (hC.1 _ _ e0.symm.toRingEquiv _)
  exact ⟨⟨n, RingHom.ker f, hg⟩, e0.symm, hcomp⟩

theorem diag_nonempty (hC : LeafComp) (hS : LeafSup) (hQ : LeafCoeq) (A : Type) [CommRing A] (I : Ideal A) :
    Nonempty (Diag A I) := by
  have hf : IsFiltered (Obj I) :=
    { cocone_objs := fun X Y => by
        obtain ⟨T, _, u, u', huu, hg⟩ := hS _ _ _ X.s Y.s I X.good Y.good
        obtain ⟨Z, ρ, hρ⟩ := key hC _ hg
        refine ⟨Z, ⟨ρ.comp u, by rw [RingHom.comp_assoc, hρ]⟩, ⟨ρ.comp u', ?_⟩, trivial⟩
        rw [RingHom.comp_assoc, ← huu, hρ]
      cocone_maps := fun X Y f g => by
        obtain ⟨T, _, w, hw, hg⟩ := hQ _ _ _ X.s Y.s I f.1 g.1 X.good Y.good f.2 g.2
        obtain ⟨Z, ρ, hρ⟩ := key hC _ hg
        refine ⟨Z, ⟨ρ.comp w, by rw [RingHom.comp_assoc, hρ]⟩, Subtype.ext ?_⟩
        change (ρ.comp w).comp f.1 = (ρ.comp w).comp g.1
        rw [RingHom.comp_assoc, RingHom.comp_assoc, hw]
      nonempty := by
        obtain ⟨Z, _, _⟩ := key hC (RingHom.id A) (hC.1 A A (RingEquiv.refl A) I)
        exact ⟨Z⟩ }
  refine ⟨@Diag.mk A _ I (Obj I) _ hf DF (fun X => X.s) (fun e => e.2) (fun X => X.good) ?_⟩
  intro j S _ ψ hψ
  have hg : Good (ψ.comp j.s) I := hC.2 _ _ _ _ _ _ j.good hψ
  obtain ⟨Z, ρ, hρ⟩ := key hC _ hg
  exact ⟨Z, ⟨ρ.comp ψ, hρ⟩, ρ, rfl⟩

end LateralTheory.CohomologicalPurity.Hz.DiagPf

namespace LateralTheory.CohomologicalPurity.Hz

theorem LeafDiag_of (hC : LeafComp) (hS : LeafSup) (hQ : LeafCoeq) : LeafDiag :=
  fun A _ I => DiagPf.diag_nonempty hC hS hQ A I

end LateralTheory.CohomologicalPurity.Hz
end
end
end

-- Source module: Development.EtaleCohomology.CohomologicalPurity.LeafHensCut

section

@[expose] public section

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Hz

theorem Good.nbhd {A S : Type} [CommRing A] [CommRing S] {φ : A →+* S} {I : Ideal A} (h : Good φ I) : Nbhd φ I := by
  refine ⟨h.etale, Ideal.quotientMap_injective' ?_, fun y => ?_⟩
  · obtain ⟨r, hr⟩ := h.retr
    have h1 : I.map φ ≤ RingHom.ker r := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change (r.comp φ) a = 0
      rw [hr]
      exact Ideal.Quotient.eq_zero_iff_mem.2 ha
    intro a ha
    have h2 : (r.comp φ) a = 0 := h1 ha
    rw [hr] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.1 h2
  · obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := h.surj s
    refine ⟨Ideal.Quotient.mk I a, ?_⟩
    rw [Ideal.quotientMap_mk]
    exact (Ideal.Quotient.eq.2 ha).symm

theorem exists_obj (h1 : LeafDiag) (h2 : LeafColHens) (h3 : LeafColUniv) (A : Type) [CommRing A] (I : Ideal A) :
    ∃ (H : CommRingCat.{0}) (η : A →+* H), HenselianRing H (I.map η) ∧ IndNbhd η I ∧ Univ η I := by
  obtain ⟨Δ⟩ := h1 A I
  let c := colimit.cocone Δ.D
  have hc : IsColimit c := colimit.isColimit Δ.D
  obtain ⟨j₀⟩ : Nonempty Δ.J := IsFiltered.nonempty
  have hw : ∀ {j k : Δ.J} (e : j ⟶ k), (Δ.leg c j).comp (Δ.s j) = (Δ.leg c k).comp (Δ.s k) := fun {j k} e => by
    have h : (Δ.leg c k).comp (Δ.D.map e).hom = Δ.leg c j := congrArg CommRingCat.Hom.hom (c.w e)
    rw [← Δ.nat e, ← RingHom.comp_assoc, h]
  have hη : ∀ j, (Δ.leg c j).comp (Δ.s j) = (Δ.leg c j₀).comp (Δ.s j₀) := fun j =>
    (hw (IsFiltered.leftToMax j j₀)).trans (hw (IsFiltered.rightToMax j j₀)).symm
  refine ⟨c.pt, _, h2 A I Δ c hc _ hη, ?_, h3 A I Δ c hc _ hη⟩
  refine ⟨Δ.J, Δ.cat, Δ.filt, Δ.D, ⟨fun j => CommRingCat.ofHom (Δ.s j), fun j k e => ?_⟩, c.ι, ⟨hc⟩,
    fun j => ⟨(Δ.good j).nbhd, ?_⟩⟩
  · exact CommRingCat.hom_ext (Δ.nat e).symm
  · exact CommRingCat.hom_ext (hη j)

theorem goal_of (h1 : LeafDiag) (h2 : LeafColHens) (h3 : LeafColUniv) : LeafHens := by
  choose H η hh hi hu using exists_obj h1 h2 h3
  have key : ∀ {A B : Type} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B} (φ : A →+* B), I ≤ J.comap φ →
      ∃! χ : H A I →+* H B J, χ.comp (η A I) = (η B J).comp φ := fun {A B} _ _ {I J} φ h =>
    hu A I _ _ (hh B J) _ fun a ha => Ideal.mem_map_of_mem (η B J) (h ha)
  refine ⟨⟨H, η, fun φ h => (key φ h).exists.choose, fun φ h => (key φ h).exists.choose_spec, fun A _ I h => ?_,
    fun φ ψ h h' h'' => ?_, hh, hi⟩⟩
  · exact (key _ h).unique (key _ h).exists.choose_spec rfl
  · refine (key _ h'').unique (key _ h'').exists.choose_spec ?_
    rw [RingHom.comp_assoc, (key φ h).exists.choose_spec, ← RingHom.comp_assoc, (key ψ h').exists.choose_spec,
      RingHom.comp_assoc]

end LateralTheory.CohomologicalPurity.Hz
end
end
end

-- Source module: Development.EtaleCohomology.CohomologicalPurity.LeafRootHensPf

section

@[expose] public section

noncomputable section
open Polynomial

namespace LateralTheory.CohomologicalPurity.Hz

theorem hens_isUnit_of_mk {B : Type} [CommRing B] (J : Ideal B) (hJ : J ≤ Ideal.jacobson ⊥) (x : B)
    (hx : IsUnit (Ideal.Quotient.mk J x)) : IsUnit x := by
  obtain ⟨y, hy⟩ := (Ideal.Quotient.mk_surjective (hx.unit⁻¹ : (B ⧸ J)ˣ).1)
  have h1 : Ideal.Quotient.mk J (x * y) = Ideal.Quotient.mk J 1 := by
    rw [map_mul, hy, map_one]; exact hx.mul_val_inv
  have h2 : x * y - 1 ∈ J := Ideal.Quotient.eq.mp h1
  have h3 : IsUnit (x * y) := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hJ h2)
  exact isUnit_of_mul_isUnit_left h3

theorem hens_isUnit_of_sub {B : Type} [CommRing B] (J : Ideal B) (hJ : J ≤ Ideal.jacobson ⊥) (x y : B)
    (hxy : x - y ∈ J) (hy : IsUnit (Ideal.Quotient.mk J y)) : IsUnit x := by
  apply hens_isUnit_of_mk J hJ
  have : Ideal.Quotient.mk J x = Ideal.Quotient.mk J y := Ideal.Quotient.eq.mpr hxy
  rwa [this]

theorem hens_eval_sub_mem {B : Type} [CommRing B] (J : Ideal B) (p : B[X]) (x y : B) (h : x - y ∈ J) :
    p.eval x - p.eval y ∈ J := by
  obtain ⟨k, hk⟩ := Polynomial.sub_dvd_eval_sub x y p
  rw [hk]; exact J.mul_mem_right k h

theorem hens_q_eval {A : Type} [CommRing A] (f : A[X]) (a : A) (hf : f.Monic) :
    (f /ₘ (X - C a)).eval a = f.derivative.eval a := by
  have h : C (f.eval a) + (X - C a) * (f /ₘ (X - C a)) = f := by
    rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval]; exact Polynomial.modByMonic_add_div f _
  conv_rhs => rw [← h]
  simp [derivative_mul]

theorem LeafRootHens_of : LeafRootHens := by
  intro A B _ _ I J hJ ψ hIJ f a hf hfa hu
  have hjac : J ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.jacobson_bot]
    exact hJ.jac
  have hmk : ∀ x : A, IsUnit (Ideal.Quotient.mk I x) → IsUnit (Ideal.Quotient.mk J (ψ x)) := by
    intro x hx
    have := hx.map (Ideal.quotientMap J ψ hIJ)
    simpa [Ideal.quotientMap_mk] using this
  have hder : ∀ z : B, (f.map ψ).derivative.eval z = (f.derivative.map ψ).eval z := by
    intro z; rw [Polynomial.derivative_map]
  have e0 : ∀ (p : A[X]), (p.map ψ).eval (ψ a) = ψ (p.eval a) := by
    intro p; rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have hev0 : (f.map ψ).eval (ψ a) ∈ J := by rw [e0]; exact hIJ hfa
  have hu0 : IsUnit (Ideal.Quotient.mk J ((f.map ψ).derivative.eval (ψ a))) := by
    rw [hder, e0]; exact hmk _ hu
  obtain ⟨c, hc, hca⟩ := hJ.is_henselian (f.map ψ) (hf.map ψ) (ψ a) hev0 hu0
  have hc1 : IsUnit ((f.derivative.map ψ).eval c) := by
    apply hens_isUnit_of_sub J hjac _ (ψ (f.derivative.eval a)) _ (hmk _ hu)
    rw [← e0]; exact hens_eval_sub_mem J _ c (ψ a) hca
  have hc2 : IsUnit (((f /ₘ (X - C a)).map ψ).eval c) := by
    apply hens_isUnit_of_sub J hjac _ (ψ (f.derivative.eval a)) _ (hmk _ hu)
    rw [← hens_q_eval f a hf, ← e0]; exact hens_eval_sub_mem J _ c (ψ a) hca
  refine ⟨c, hc, hca, hc1, hc2, ?_⟩
  intro c' hc' hc'a
  have hd : c' - c ∈ J := by
    have := J.sub_mem hc'a hca
    rwa [sub_sub_sub_cancel_right] at this
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (f.map ψ) c (c' - c)
  rw [add_sub_cancel, hc'.eq_zero, hc.eq_zero, zero_add] at hk
  have hfac : (c' - c) * ((f.map ψ).derivative.eval c + k * (c' - c)) = 0 := by
    rw [hk]; ring
  have hunit : IsUnit ((f.map ψ).derivative.eval c + k * (c' - c)) := by
    apply hens_isUnit_of_sub J hjac _ ((f.map ψ).derivative.eval c)
    · rw [add_sub_cancel_left]; exact J.mul_mem_left k hd
    · rw [hder]; exact hc1.map _
  have : c' - c = 0 := (hunit.mul_left_eq_zero).mp hfac
  exact sub_eq_zero.mp this

end LateralTheory.CohomologicalPurity.Hz
end
end
end

-- Source module: Development.EtaleCohomology.CohomologicalPurity.FinLeafHens

section

@[expose] public section

namespace LateralTheory.Fin.LeafHens
theorem henselization_compatible_maps_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafComp := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafComp_of
theorem henselization_inverse_limit_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafInv := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafInv_of
theorem standard_etale_simple_root_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafRootStd := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafRootStd_of
theorem henselian_simple_root_lift_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafRootHens := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafRootHens_of
theorem henselization_simple_root_lift_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafRoot := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafRoot_of <;> first | exact standard_etale_simple_root_of_henselization | exact henselian_simple_root_lift_of_henselization
theorem henselization_supremum_neighborhood_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafSup := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafSup_of
theorem henselization_coequalizer_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafCoeq := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafCoeq_of <;> first | exact henselization_inverse_limit_of_henselization | exact henselization_compatible_maps_of_henselization
theorem henselization_diagonal_section_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafDiag := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafDiag_of <;> first | exact henselization_compatible_maps_of_henselization | exact henselization_supremum_neighborhood_of_henselization | exact henselization_coequalizer_of_henselization
theorem henselization_etale_neighborhood_stage_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafStage := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafStage_of
theorem henselization_colimit_henselian_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafColHens := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafColHens_of <;> first | exact henselization_etale_neighborhood_stage_of_henselization | exact henselization_inverse_limit_of_henselization | exact henselization_simple_root_lift_of_henselization
theorem henselization_colimit_universal_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafColUniv := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafColUniv_of
theorem etale_purity_henselian_local_of_henselization : LateralTheory.CohomologicalPurity.LeafHens := by
  apply LateralTheory.CohomologicalPurity.Hz.goal_of <;> first | exact henselization_compatible_maps_of_henselization | exact henselization_inverse_limit_of_henselization | exact henselization_simple_root_lift_of_henselization | exact henselization_supremum_neighborhood_of_henselization | exact henselization_coequalizer_of_henselization | exact henselization_diagonal_section_of_henselization | exact henselization_etale_neighborhood_stage_of_henselization | exact henselization_colimit_henselian_of_henselization | exact henselization_colimit_universal_of_henselization
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafHens := etale_purity_henselian_local_of_henselization
end LateralTheory.Fin.LeafHens
end
end
