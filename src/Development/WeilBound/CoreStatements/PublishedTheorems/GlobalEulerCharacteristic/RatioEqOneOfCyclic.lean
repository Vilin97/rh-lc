module

public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.GlobalEulerFormulaInf
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkKilledC
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShapiroCoind
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.DefsForms
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
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linter.Style

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkCoinfB

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_coinf_b

theorem uliftInt_smul {A : Type} [AddCommGroup A] (inst : Module (ULift.{0} ℤ) A) (c : ULift.{0} ℤ) (a : A) :
    inst.smul c a = c.down • a := by
  obtain ⟨n⟩ := c
  have h := Int.cast_smul_eq_zsmul (R := ULift.{0} ℤ) (M := A) n a
  have hn : ((n : ℤ) : ULift.{0} ℤ) = ⟨n⟩ := by ext; simp
  rw [hn] at h
  exact h

section Equiv

variable {G Γ : Type} [Group G] [Group Γ] (π : G →* Γ) (hπ : Function.Surjective π) (D : Subgroup Γ)
  (W : Subgroup G) (hW : W = D.comap π)

noncomputable def cosetEquiv : G ⧸ W ≃ Γ ⧸ D :=
  (Subgroup.quotientEquivOfEq hW).trans (quotientComapEquiv D hπ)

theorem cosetEquiv_mk (g : G) :
    cosetEquiv π hπ D W hW (QuotientGroup.mk g) = QuotientGroup.mk (π g) := rfl

theorem cosetEquiv_smul (g : G) (x : G ⧸ W) :
    cosetEquiv π hπ D W hW (g • x) = π g • cosetEquiv π hπ D W hW x := by
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [MulAction.Quotient.smul_mk, cosetEquiv_mk, cosetEquiv_mk, MulAction.Quotient.smul_mk,
      smul_eq_mul, smul_eq_mul, map_mul]

theorem cosetEquiv_symm_smul (g : G) (y : Γ ⧸ D) :
    (cosetEquiv π hπ D W hW).symm (π g • y) = g • (cosetEquiv π hπ D W hW).symm y := by
  apply (cosetEquiv π hπ D W hW).injective
  rw [cosetEquiv_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end Equiv

local notation "ℚ̄" => AlgebraicClosure ℚ


theorem coind_eq_infl_funRep (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    [hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal]
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module (ZMod ℓ) M]
    (ρ : Representation (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) M)
    (hρ : ∀ (g : galUnramifiedOutside K.1 ℚ̄ S) (m : M), ρ (QuotientGroup.mk g) m = M.ρ g m)
    (D : Subgroup (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))))
    (L' : FiniteSubfield) [Fact (K ≤ L')]
    (hL' : ∀ x : L'.1, algebraMap L'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hW : (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) = D.comap (QuotientGroup.mk' _)) :
    gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) ιr =
      (haveI := W_killed_c.isDiscreteRep_infl (gsOpenSubgroup S hL) (funRep ((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ⧸ D) ρ); gsEulerRatio S (W_killed_c.infl (gsOpenSubgroup S hL) (funRep ((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ⧸ D) ρ)) ιr) := by
  have hπ : Function.Surjective (QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) :=
    QuotientGroup.mk'_surjective _
  let E := cosetEquiv _ hπ D _ hW
  letI i1 : Module (ULift.{0} ℤ) ((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) → M) :=
    (funDiagRep (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) M).hV2
  letI i2 : Module (ULift.{0} ℤ) (((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ⧸ D) → M) :=
    (W_killed_c.infl (gsOpenSubgroup S hL) (funRep ((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ⧸ D) ρ)).hV2
  let eqv : (funDiagRep (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) M).ρ.Equiv
      (W_killed_c.infl (gsOpenSubgroup S hL) (funRep ((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ⧸ D) ρ)).ρ :=
    { toLinearEquiv :=
        { toFun := fun F y => F (E.symm y)
          invFun := fun F x => F (E x)
          map_add' := fun F F' => rfl
          map_smul' := fun c F => by
            funext y
            exact uliftInt_smul _ c (F (E.symm y))
          left_inv := fun F => by funext x; simp
          right_inv := fun F => by funext y; simp }
      isIntertwining' := fun g => by
        refine LinearMap.ext fun F => funext fun y => ?_
        change M.ρ g (F (g⁻¹ • E.symm y)) = ρ (QuotientGroup.mk g) (F (E.symm ((QuotientGroup.mk g : galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))⁻¹ • y)))
        rw [hρ]
        congr 2
        have := cosetEquiv_symm_smul _ hπ D _ hW g⁻¹ y
        exact this.symm }
  haveI := W_killed_c.isDiscreteRep_infl (gsOpenSubgroup S hL) (funRep ((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ⧸ D) ρ)
  exact gsEulerRatio_eq_of_iso S _ ιr (coindResIsoFunDiagRep (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) M ≪≫ Rep.mkIso eqv)

end PositivityTheory.Lit1.GEN.W_coinf_b
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkQuotV

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.QuotientActionGlobalEulerCharacteristic

open W_killed_c

local notation "ℚ̄" => AlgebraicClosure ℚ

def addAct {G : Type} [Group G] (M : Rep.{0} (ULift.{0} ℤ) G) : G →* AddMonoid.End M where
  toFun g := (M.ρ g).toAddMonoidHom
  map_one' := by ext x; simp <;> rfl
  map_mul' g h := by ext x; simp <;> rfl

def zmodRep (n : ℕ) {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod n) V] (φ : G →* AddMonoid.End V) :
    Representation (ZMod n) G V where
  toFun g := (φ g).toZModLinearMap n
  map_one' := by ext x; simp <;> rfl
  map_mul' g h := by ext x; simp only [map_mul]; rfl

theorem nonempty_iso_of_addEquiv {k G : Type} [CommRing k] [Group G] (hk : Function.Surjective (Int.cast : ℤ → k))
    (A B : Rep.{0} k G) (e : A ≃+ B) (h : ∀ (g : G) (x : A), e (A.ρ g x) = B.ρ g (e x)) : Nonempty (A ≅ B) := by
  let f : A ≃ₗ[k] B :=
    { e with
      map_smul' := fun c x => by
        obtain ⟨n, rfl⟩ := hk c
        show e ((n : k) • x) = (n : k) • e x
        rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul] }
  exact ⟨Rep.mkIso (Representation.Equiv.mk f fun g => LinearMap.ext fun x => h g x)⟩


theorem quotient_representation_open (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    [hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal]
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module (ZMod ℓ) M]
    (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1) :
    ∃ (ρ : Representation (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) M),
      (∀ (g : galUnramifiedOutside K.1 ℚ̄ S) (m : M), ρ (QuotientGroup.mk g) m = M.ρ g m) ∧
      gsEulerRatio S M ιr = (haveI := isDiscreteRep_infl (gsOpenSubgroup S hL) ρ; gsEulerRatio S (infl (gsOpenSubgroup S hL) ρ) ιr) := by
  have hker : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (zmodRep ℓ (addAct M)).ker := fun g hg => by
    rw [MonoidHom.mem_ker]
    ext x
    change (M.ρ g) x = x
    rw [htriv g hg]
    rfl
  let ρ : Representation (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) M :=
    QuotientGroup.lift _ (zmodRep ℓ (addAct M)) hker
  refine ⟨ρ, fun g m => rfl, ?_⟩
  haveI := isDiscreteRep_infl (gsOpenSubgroup S hL) ρ
  obtain ⟨e⟩ := nonempty_iso_of_addEquiv (k := ULift.{0} ℤ) (fun c => ⟨c.down, rfl⟩) M (infl (gsOpenSubgroup S hL) ρ)
    (AddEquiv.refl M) (fun _ _ => rfl)
  exact gsEulerRatio_eq_of_iso S M ιr e

theorem quot_rep (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    [hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal]
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M]
    (hℓ : ∀ m : M, ℓ • m = 0) (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1) :
    ∃ (_ : Module (ZMod ℓ) M) (ρ : Representation (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) M),
      (∀ (g : galUnramifiedOutside K.1 ℚ̄ S) (m : M), ρ (QuotientGroup.mk g) m = M.ρ g m) ∧
      gsEulerRatio S M ιr = (haveI := isDiscreteRep_infl (gsOpenSubgroup S hL) ρ; gsEulerRatio S (infl (gsOpenSubgroup S hL) ρ) ιr) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  letI inst : Module (ZMod ℓ) M := AddCommGroup.zmodModule hℓ
  exact ⟨inst, quotient_representation_open ℓ K S ιr L hL M htriv⟩

end PositivityTheory.Lit1.GEN.QuotientActionGlobalEulerCharacteristic
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.RatioEqOneOfCyclic

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_killed_c

section GS

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem ratio_eq_one_of_cyclic (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (hS : S.Finite)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hℓ : ∀ m : M, ℓ • m = 0) (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1)
    (hcyc : ∀ (L' : FiniteSubfield) [Fact (K ≤ L')]
      (hL' : ∀ x : L'.1, algebraMap L'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) → IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) →
      gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) ιr = 1) :
    gsEulerRatio S M ιr = 1 := by
  haveI := hN
  haveI := finite_quot_gs K S L hL
  obtain ⟨inst, ρ, hρ, he⟩ := QuotientActionGlobalEulerCharacteristic.quot_rep ℓ K S ιr L hL M hℓ htriv
  rw [he]
  exact eq_one_of_forall_isCyclic (gsOpenSubgroup S hL) (gs_multKilled ℓ K S hS hSℓ ιr)
    (gs_posKilled ℓ K S hS hSℓ ιr) ρ (fun D hD' => by
      obtain ⟨L', hKL', hL', hW, hle, hcycW⟩ := exists_field_of_cyclic ℓ K S ιr L hL D hD'
      have := hcyc L' hL' hle hcycW
      rw [W_coinf_b.coind_eq_infl_funRep ℓ K S ιr L hL M ρ hρ D L' hL' hW] at this
      exact this)

end GS

end PositivityTheory.Lit1.GEN.W_killed_c
end
end
