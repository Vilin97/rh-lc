module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AutCongrContinuousCycInertia
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSSRepMapOfAbsIrrDistinct
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesOfExact
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

-- Source module: Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CharPolyRootsConstruction

section

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

def SameSS {k Γ V W : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W) : Prop :=
  ∃ (s : CompositionSeries (Submodule (MonoidAlgebra k Γ) ρ.asModule))
    (t : CompositionSeries (Submodule (MonoidAlgebra k Γ) σ.asModule)),
    s.head = ⊥ ∧ s.last = ⊤ ∧ t.head = ⊥ ∧ t.last = ⊤ ∧
    ∃ f : Fin s.length ≃ Fin t.length, ∀ j : Fin s.length,
      Nonempty ((↥(s j.succ) ⧸ (s j.castSucc).submoduleOf (s j.succ)) ≃ₗ[MonoidAlgebra k Γ]
        (↥(t (f j).succ) ⧸ (t (f j).castSucc).submoduleOf (t (f j).succ)))

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

section HidaSetting

variable (N : NData R H what₂) (i : N.Loc)
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))

def repBar (x : N.X i) : Representation (kk N i) (GE N) (Fin R.nV → kk N i) :=
  matRep (mapM (IsLocalRing.residue (N.O i)) (rO N i r x))

def ContSemisimple : Prop :=
  ∀ x, Continuous (fun g => rO N i r x g) ∧ IsSS (repK N i r x)

def CharPolyInT : Prop :=
  ∀ (h : GE N) (d : ℕ),
    (fun x => (Matrix.det (1 - (X : (N.O i)[X]) • (rO N i r x h).map (C (R := N.O i)))).coeff d) ∈ N.T i

def Constituents : Prop :=
  (∀ x, AbsIrrDistinct (repK N i r x)) ∧
  (∀ x y, SameSS (repBar N i r x) (repBar N i r y)) ∧
  (∀ x (h : GE N), ∃ s : Multiset (kk N i),
    ((rO N i r x h).map (IsLocalRing.residue (N.O i))).charpoly = (s.map fun a => X - C a).prod)

def ThetaShape : Prop :=
  ∀ x ∈ N.Z i,
    (∃ e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)),
      ∀ g u, e ((mapM (toK N i) (rO N i r x) g).mulVec u) =
        ((mapM (toK N i) (rhoO N i ρ x) g).mulVec (e u).1,
          fun c : Fin R.t => toK N i ((N.chi i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (e u).2 c)) ∧
    AbsIrrSub (mapRep (IsLocalRing.residue (N.O i)) (ρ x)) ⊤

def HidaSetting : Prop :=
  ContSemisimple N i r ∧ CharPolyInT N i r ∧ Constituents N i r ∧ ThetaShape N i r ρ

end HidaSetting

section Enlarge

variable (N : NData R H what₂) (i : N.Loc) (N₁ : NData R H what₂) (i₁ : N₁.Loc)
  (σ : N.Om ≃ₐ[H.E] N₁.Om) (φ : N.O i →+* N₁.O i₁) (β : N.X i ≃ N₁.X i₁)

variable {N i N₁ i₁}

end Enlarge

end GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimplificationUniqueUpToConj

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

noncomputable def bnMatRep {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W) :
    Γ →* GL (Fin a) k :=
  MonoidHom.toHomUnits
    (((LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom.toMonoidHom).comp s)

theorem bnMatRep_val {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W) (g : Γ) :
    ((bnMatRep b s g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)
      = LinearMap.toMatrix b b (s g) := rfl

theorem bnMatRep_mulVec {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W) (g : Γ)
    (v : W) :
    ((bnMatRep b s g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).mulVec (b.equivFun v)
      = b.equivFun (s g v) := by
  rw [bnMatRep_val]
  exact LinearMap.toMatrix_mulVec_repr b b (s g) v

theorem bnMatRep_isSSRep {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W)
    (hs : IsSS s) : IsSSRep (bnMatRep b s) := by
  intro U hU
  obtain ⟨U', hU', hc⟩ := hs (U.comap (b.equivFun : W →ₗ[k] (Fin a → k))) (by
    intro g v hv
    have := hU g _ hv
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at this ⊢
    rw [← bnMatRep_mulVec]
    exact this)
  refine ⟨U'.map (b.equivFun : W →ₗ[k] (Fin a → k)), ?_, ?_⟩
  · rintro g _ ⟨v, hv, rfl⟩
    refine ⟨s g v, hU' g v hv, ?_⟩
    exact (bnMatRep_mulVec b s g v).symm
  · have h := (Submodule.orderIsoMapComap b.equivFun).isCompl hc
    have h1 : (Submodule.orderIsoMapComap b.equivFun)
        (U.comap (b.equivFun : W →ₗ[k] (Fin a → k))) = U :=
      Submodule.map_comap_eq_of_surjective b.equivFun.surjective U
    rw [h1] at h
    exact h

theorem brauerNesbitt_abstract_of_matrix : (∀ (Γ k : Type) [Group Γ] [Field k] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) k), IsSSRep ρ → IsSSRep ρ' → (∀ g, ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly = ((ρ' g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) → ∃ h : GL (Fin a) k, ∀ g, ρ' g = h * ρ g * h⁻¹) → ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (s : Representation k Γ W) (s' : Representation k Γ V), IsSS s → IsSS s' → (∀ g, LinearMap.charpoly (s g) = LinearMap.charpoly (s' g)) → ∃ e : W ≃ₗ[k] V, ∀ g v, e (s g v) = s' g (e v) := by
  intro H k Γ _ _ W _ _ _ V _ _ _ s s' hs hs' hc
  have hdim : Module.finrank k V = Module.finrank k W := by
    rw [← LinearMap.charpoly_natDegree (s 1), ← LinearMap.charpoly_natDegree (s' 1), hc]
  let b : Module.Basis (Fin (Module.finrank k W)) k W := Module.finBasis k W
  let b' : Module.Basis (Fin (Module.finrank k W)) k V := Module.finBasisOfFinrankEq k V hdim
  obtain ⟨h, hh⟩ := H Γ k _ (bnMatRep b s) (bnMatRep b' s') (bnMatRep_isSSRep b s hs)
    (bnMatRep_isSSRep b' s' hs') (by
      intro g
      rw [bnMatRep_val, bnMatRep_val, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix, hc])
  let m : (Fin (Module.finrank k W) → k) ≃ₗ[k] (Fin (Module.finrank k W) → k) :=
    (Matrix.GeneralLinearGroup.toLin h).toLinearEquiv
  have hm : ∀ x, m x = (h : Matrix _ _ k).mulVec x := fun x => rfl
  refine ⟨b.equivFun.trans (m.trans b'.equivFun.symm), fun g v => ?_⟩
  apply b'.equivFun.injective
  rw [← bnMatRep_mulVec]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hm]
  rw [← bnMatRep_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul,
    ← Units.val_mul, hh g, inv_mul_cancel_right]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthOfFiniteDimensional

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Polynomial

noncomputable section
namespace GlobalTheory.ConsCompare

section Factors
open GlobalTheory.AdmLoc
variable {k A : Type} [Field k] [Ring A] [Algebra k A]

theorem finiteLength_of_finiteDimensional (k : Type) [Field k] [Algebra k A] (M : Type) [AddCommGroup M]
    [Module k M] [Module A M] [IsScalarTower k A M] [FiniteDimensional k M] : IsFiniteLength A M := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩

theorem exists_semisimple_sameFactors : ∀ (d : ℕ) (M : Type) [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] [FiniteDimensional k M], Module.finrank k M = d →
    ∃ (S : Type) (_ : AddCommGroup S) (_ : Module k S) (_ : Module A S) (_ : IsScalarTower k A S)
      (_ : FiniteDimensional k S), IsSemisimpleModule A S ∧ SameFactors A M S := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ _ _ _ hd
  have hfl := finiteLength_of_finiteDimensional (A := A) k M
  rcases subsingleton_or_nontrivial M with h0 | h0
  · exact ⟨M, _, _, _, inferInstance, inferInstance, (isSemisimpleModule_iff A M).2
      (have := (Submodule.subsingleton_iff A).2 h0; Subsingleton.instComplementedLattice),
      SameFactors.refl hfl⟩
  · haveI : IsNoetherian A M := isNoetherian_of_tower k inferInstance
    obtain ⟨N, hN, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule A M)).resolve_left bot_ne_top
    have hlt : Module.finrank k N < d := by
      rw [← hd]
      exact Submodule.finrank_lt (s := N.restrictScalars k) fun h => hN.1 (by simpa using h)
    obtain ⟨S, _, _, _, _, _, hS, hf⟩ := ih _ hlt N rfl
    haveI : IsSimpleModule A (M ⧸ N) := isSimpleModule_iff_isCoatom.2 hN
    exact ⟨S × (M ⧸ N), _, _, _, inferInstance, inferInstance,
      isSemisimpleModule_of_isSemisimpleModule_submodule' (p := fun b : Bool =>
        cond b (LinearMap.range (LinearMap.inl A S (M ⧸ N))) (LinearMap.range (LinearMap.inr A S (M ⧸ N))))
        (by rintro (_ | _) <;> exact IsSemisimpleModule.range _)
        (by rw [iSup_bool_eq]; exact LinearMap.sup_range_inl_inr),
      (SameFactors.sub_prod_quot hfl N).trans
        (hf.prod (SameFactors.refl (finiteLength_of_finiteDimensional k _)))⟩

theorem cpOn_eq_of_sameFactors (a : A) {M M' : Type} [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] [FiniteDimensional k M] [AddCommGroup M'] [Module k M'] [Module A M']
    [IsScalarTower k A M'] [FiniteDimensional k M'] (h : SameFactors A M M') : cpOn k a M = cpOn k a M' := by
  obtain ⟨s, t, h1, h2, h3, h4, f, hf⟩ := h
  rw [cpOn_series _ s h1 h2, cpOn_series _ t h3 h4]
  exact Fintype.prod_equiv f _ _ fun j => cpOn_congr _ (hf j).some

variable {Γ : Type} [Group Γ]

def repOf (k Γ S : Type) [Field k] [Group Γ] [AddCommGroup S] [Module k S] [Module (MonoidAlgebra k Γ) S]
    [IsScalarTower k (MonoidAlgebra k Γ) S] : Representation k Γ S :=
  (Algebra.lsmul k k S : MonoidAlgebra k Γ →ₐ[k] Module.End k S).toMonoidHom.comp (MonoidAlgebra.of k Γ)

theorem isSS_repOf {S : Type} [AddCommGroup S] [Module k S] [Module (MonoidAlgebra k Γ) S]
    [IsScalarTower k (MonoidAlgebra k Γ) S] [IsSemisimpleModule (MonoidAlgebra k Γ) S] :
    IsSS (repOf k Γ S) := fun W hW => by
  let W₁ : Submodule (MonoidAlgebra k Γ) S :=
    { W.toAddSubmonoid with
      smul_mem' := fun a v hv => by
        induction a using MonoidAlgebra.induction_on with
        | of g => exact hW g v hv
        | add a b ha hb => rw [add_smul]; exact W.add_mem ha hb
        | smul c a ha => rw [smul_assoc]; exact W.smul_mem c ha }
  obtain ⟨W₂, h⟩ := exists_isCompl W₁
  refine ⟨W₂.restrictScalars k, fun g v hv => W₂.smul_mem (MonoidAlgebra.of k Γ g) hv, ?_⟩
  exact (Submodule.isCompl_restrictScalars_iff k (s := W₁)).2 h

theorem sameSS_of_charpoly_eq (hBN : GlobalTheory.ConstituentsCompare.BrauerNesbitt) {V W : Type} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W)
    (h : ∀ g, LinearMap.charpoly (ρ g) = LinearMap.charpoly (σ g)) : GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction.SameSS ρ σ := by
  have : FiniteDimensional k ρ.asModule := inferInstanceAs (FiniteDimensional k V)
  have : FiniteDimensional k σ.asModule := inferInstanceAs (FiniteDimensional k W)
  have e1 : ∀ g, LinearMap.charpoly (ρ g) = cpOn k (MonoidAlgebra.of k Γ g) ρ.asModule := fun g => by
    unfold cpOn
    rw [← LinearEquiv.charpoly_conj ρ.asModuleEquiv]
    congr 1
    ext v
    simp [LinearEquiv.conj_apply]
    rfl
  have e2 : ∀ g, LinearMap.charpoly (σ g) = cpOn k (MonoidAlgebra.of k Γ g) σ.asModule := fun g => by
    unfold cpOn
    rw [← LinearEquiv.charpoly_conj σ.asModuleEquiv]
    congr 1
    ext v
    simp [LinearEquiv.conj_apply]
    rfl
  obtain ⟨S, _, _, _, _, _, hS, hf⟩ :=
    exists_semisimple_sameFactors (k := k) (A := MonoidAlgebra k Γ) _ ρ.asModule rfl
  obtain ⟨S', _, _, _, _, _, hS', hf'⟩ :=
    exists_semisimple_sameFactors (k := k) (A := MonoidAlgebra k Γ) _ σ.asModule rfl
  obtain ⟨e, he⟩ := GlobalTheory.brauerNesbitt_abstract_of_matrix hBN (repOf k Γ S) (repOf k Γ S') isSS_repOf isSS_repOf
    fun g => ((cpOn_eq_of_sameFactors _ hf).symm.trans ((e1 g).symm.trans ((h g).trans (e2 g)))).trans
      (cpOn_eq_of_sameFactors _ hf')
  let e' : S ≃ₗ[MonoidAlgebra k Γ] S' :=
    { e.toAddEquiv with
      map_smul' := fun a v => by
        show e (a • v) = a • e v
        induction a using MonoidAlgebra.induction_on with
        | of g => exact he g v
        | add a b ha hb => rw [add_smul, add_smul, map_add (f := _), ha, hb]
        | smul c a ha => rw [smul_assoc, smul_assoc, map_smul, ha] }
  exact (hf.trans (SameFactors.of_equiv hf.finiteLength_right e')).trans hf'.symm

end Factors

section Distinct
open Matrix

end Distinct

section BaseChange
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

variable {Γ X A B : Type} [Group Γ] [CommRing A] [CommRing B] {n r t : ℕ}

variable [Algebra A B]

variable [IsDomain A] [IsDomain B]

variable [IsLocalRing A] [IsLocalRing B]

end BaseChange

end GlobalTheory.ConsCompare
end
end
end
