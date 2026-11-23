module

import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentiallySemistableType
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TotallySplit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitAdelicMatrixLocalComponentStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardAdelicAddCharStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageOfIsCuspFormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalUpperUnipotentAdelicUpperUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerLawUpperTriangularUnipotentAdelicStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.RingTheory.SimpleRing.Principal
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTypeVLoc
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialOfIsSubquotient

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharsOfTameLpDim

section

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TameInertiaChars

theorem exists_basis_eigen {n : ℕ} {Γ : Type} (f : Γ → Module.End ℂ (Fin n → ℂ))
    (hs : ∀ g, (f g).IsSemisimple) (hc : ∀ g k, Commute (f g) (f k)) :
    ∃ B : Module.Basis (Fin n) ℂ (Fin n → ℂ), ∀ j g, ∃ c : ℂ, f g (B j) = c • B j := by
  have h1 := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun g k _ => hc g k) fun g => Module.End.iSup_maxGenEigenspace_eq_top _
  simp only [fun g => (hs g).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at h1
  let T : Set (Fin n → ℂ) := {v | ∀ g, ∃ c : ℂ, f g v = c • v}
  have h2 : ⊤ ≤ Submodule.span ℂ T := by
    rw [← h1]
    exact iSup_le fun χ v hv => Submodule.subset_span fun g =>
      ⟨χ g, Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv g)⟩
  let B := Module.Basis.ofSpan h2
  have h3 := Module.Basis.ofSpan_subset h2
  refine ⟨B.reindex (B.indexEquiv (Pi.basisFun ℂ (Fin n))), fun j => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact h3 ⟨_, rfl⟩

theorem charpoly_of_basis {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (B : Module.Basis (Fin n) ℂ (Fin n → ℂ))
    (c : Fin n → ℂ) (hB : ∀ j, f (B j) = c j • B j) : f.charpoly = ∏ j, (X - C (c j)) := by
  rw [← LinearMap.charpoly_toMatrix f B, ← Matrix.charpoly_diagonal]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, hB, map_smul, B.repr_self, Matrix.diagonal_apply]
  by_cases e : i = j
  · subst e; simp
  · simp [Finsupp.single_apply, Ne.symm e, e]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end GlobalTheory.TameInertiaChars

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericSubquotientPrincipalSeries

section

@[expose] public section

open NumberField IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CuspDetBlocks

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.Whittaker


open GlobalTheory.CuspGeneric GlobalTheory.CuspRep.Generic in
theorem exists_isGeneric_subrep {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (P : CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (S : Subrepresentation (P.locRep w)) (hS : S.toSubmodule ≠ ⊥) :
    ∃ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ ∧ ψ ≠ 1 ∧ IsGeneric ψ S.toRepresentation := by
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_standardAdelicAddChar E
  have hg : ∀ v : P.V, Good ψ (a - 1) v.1.1 := fun v => GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ v.1 (P.cusp _ v.2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  obtain ⟨v₀, hv₀S, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  have hv1 : v₀.1.1 ≠ 0 := fun h => hv₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)
  obtain ⟨h, gw, e, hc⟩ := GlobalTheory.T.exists_split_adelicMatrix_localComponent E a w g₀
  have hrt : ∀ u (v : P.V) x, whit ψ (a - 1) (P.locRep w u v).1.1 x =
      whit ψ (a - 1) v.1.1 (x * finGL E a (locGL E a w u)) := fun u v x => whit_rt _ _ _ _
  let l : P.V →ₗ[ℂ] ℂ :=
    { toFun := fun v => whit ψ (a - 1) v.1.1 h
      map_add' := fun v v' => congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h
      map_smul' := fun c v => congrFun (whit_smul (a - 1) c v.1.1) h }
  have hl : ∀ v, l v = whit ψ (a - 1) v.1.1 h := fun _ => rfl
  have hne : l (P.locRep w gw v₀) ≠ 0 := by
    rw [hl, hrt, ← e]
    exact hg₀
  have hlaw : ∀ u ∈ unipB (w.adicCompletion E) (Fin a), ∀ v : P.V,
      l (P.locRep w u v) = (locPsi hψ w (superDiag u) : ℂ) * l v := fun u hu v => by
    obtain ⟨u1, u2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
    obtain ⟨t1, t2, t3⟩ := GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent E a w u u1 u2
    have hlw := (whit_good hψ (a - 1) h0 (hg v)).1.law
    have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ _ (fun k hk => hlw k hk) _ t1 t2 h
    rw [hl, hrt, hc, this, t3, superDiag_eq_sum_pairs]
    rfl
  have hcont : Continuous (locPsi hψ w) := by
    refine Continuous.subtype_mk (hψ.cont.comp ?_) _
    exact (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E)).comp
      (CuspSub.continuous_sLoc w)
  have hne1 : locPsi hψ w ≠ 1 := fun h1 => by
    obtain ⟨y, hy⟩ := hψ.loc w
    apply hy
    have := congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)
    simpa [coe_locPsi] using this
  refine ⟨locPsi hψ w, hcont, hne1, l ∘ₗ S.toSubmodule.subtype, fun e' => hne ?_, fun u hu v => ?_⟩
  · exact LinearMap.congr_fun e' ⟨_, S.apply_mem_toSubmodule gw hv₀S⟩
  · exact hlaw u hu v.1

end GlobalTheory.CuspDetBlocks

namespace GlobalTheory.CuspDetBlocks

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.Whittaker

end GlobalTheory.CuspDetBlocks
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGlLocalComponentExponentLeOne

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.DetProd

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_isGeneric_of_isLocComp {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}
    {τ : GlobalTheory.CuspRep.CuspSub E n} {w : HeightOneSpectrum (𝓞 E)}
    {ρ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (w.adicCompletion E))} (h : τ.IsLocComp w ρ) :
    ∃ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ ∧ ψ ≠ 1 ∧ GlobalTheory.Whittaker.IsGeneric ψ ρ.ρ := by
  obtain ⟨f, hf0, hf⟩ := h
  let S : Subrepresentation (τ.locRep w) := ⟨LinearMap.range f, by
    rintro g _ ⟨v, rfl⟩
    exact ⟨ρ.ρ g v, hf g v⟩⟩
  have hS : S.toSubmodule ≠ ⊥ := fun h => hf0 (LinearMap.range_eq_bot.1 h)
  obtain ⟨ψ, hc, h1, hg⟩ := GlobalTheory.CuspDetBlocks.exists_isGeneric_subrep τ w S hS
  exact ⟨ψ, hc, h1, hg.of_surjective (σ := S.toRepresentation) ⟨f.rangeRestrict, fun g => LinearMap.ext fun v => by exact Subtype.ext (hf g v)⟩
    (LinearMap.surjective_rangeRestrict _)⟩

end GlobalTheory.ThK.DetProd

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointEigenDecomposition

section

@[expose] public section

open Polynomial

namespace GlobalTheory.CommSemisimpleChars


open Classical in
theorem card_eq_of_sum_eq {H ι κ : Type} [Monoid H] [Fintype ι] [Fintype κ]
    (a : ι → (H →* ℂ)) (c : κ → (H →* ℂ)) (h : ∀ g, ∑ j, a j g = ∑ i, c i g) (ψ : H →* ℂ) :
    (Finset.univ.filter fun j => a j = ψ).card = (Finset.univ.filter fun i => c i = ψ).card := by
  classical
  let F : Finset (H →* ℂ) := insert ψ (Finset.univ.image a ∪ Finset.univ.image c)
  have li := linearIndependent_iff'.1 (linearIndependent_monoidHom H ℂ) F
    (fun φ => ((Finset.univ.filter fun j => a j = φ).card : ℂ) - (Finset.univ.filter fun i => c i = φ).card)
  have key : ∀ {τ : Type} [Fintype τ] (e : τ → (H →* ℂ)), (∀ t, e t ∈ F) →
      ∑ φ ∈ F, ((Finset.univ.filter fun t => e t = φ).card : ℂ) • (φ : H → ℂ) = ∑ t, (e t : H → ℂ) := by
    intro τ _ e he
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := F) (g := e) (fun t _ => he t)]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.1 ht).2]), Finset.sum_const,
      Nat.cast_smul_eq_nsmul]
  have hz : ∑ φ ∈ F, (((Finset.univ.filter fun j => a j = φ).card : ℂ) -
      (Finset.univ.filter fun i => c i = φ).card) • (φ : H → ℂ) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [key a (fun j => by simp [F]), key c (fun i => by simp [F]), sub_eq_zero]
    funext g
    simp only [Finset.sum_apply]
    exact h g
  have := li hz ψ (Finset.mem_insert_self _ _)
  exact_mod_cast sub_eq_zero.1 this

end GlobalTheory.CommSemisimpleChars
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTypeV

section

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
open GlobalTheory.PRep GlobalTheory.TypeTwo.PowIrrProof
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped commutatorElement
namespace UpperTheory.V.Z.J.D.TypeVAux
private theorem exists_chars {Γ : Type} [Group Γ] {n : ℕ} (ρ : Representation ℂ Γ (Fin n → ℂ))
    (hs : ∀ g, Module.End.IsSemisimple (ρ g)) (hc : ∀ s t, ρ s * ρ t = ρ t * ρ s) :
    ∃ η : Fin n → Γ →* ℂˣ, (∀ g, (ρ g).charpoly = ∏ j, (X - C (η j g : ℂ))) ∧
      ∀ j g, ρ g = 1 → η j g = 1 := by
  obtain ⟨B, hB⟩ := GlobalTheory.TameInertiaChars.exists_basis_eigen (fun g => ρ g) hs fun g k => hc g k
  choose d hd using hB
  have hne : ∀ j, B j ≠ 0 := fun j => B.ne_zero j
  have canc : ∀ j {a b : ℂ}, a • B j = b • B j → a = b := fun j a b e =>
    smul_left_injective ℂ (hne j) e
  let c : Fin n → Γ →* ℂ := fun j =>
    { toFun := d j
      map_one' := canc j (by rw [← hd j 1, map_one, one_smul]; rfl)
      map_mul' := fun s t => canc j (by
        rw [← hd j (s * t), map_mul, Module.End.mul_apply, hd j t, map_smul, hd j s, smul_smul, mul_comm]) }
  refine ⟨fun j => (c j).toHomUnits, fun g => ?_, fun j g hg => ?_⟩
  · exact GlobalTheory.TameInertiaChars.charpoly_of_basis _ B _ fun j => hd j g
  · refine Units.ext (canc j ?_)
    show d j g • B j = (1 : ℂ) • B j
    rw [← hd j g, hg, one_smul]
    rfl
private theorem exists_perm {H : Type} [Monoid H] {n : ℕ} (a c : Fin n → H →* ℂ)
    (h : ∀ g, ∑ j, a j g = ∑ i, c i g) : ∃ e : Equiv.Perm (Fin n), ∀ i, a (e i) = c i := by
  classical
  have key : ∀ ψ : H →* ℂ, Nonempty ({i // c i = ψ} ≃ {j // a j = ψ}) := fun ψ =>
    ⟨Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      exact (GlobalTheory.CommSemisimpleChars.card_eq_of_sum_eq a c h ψ).symm)⟩
  let E := Equiv.ofFiberEquiv (f := c) (g := a) fun ψ => (key ψ).some
  exact ⟨E, fun i => Equiv.ofFiberEquiv_map _ i⟩
private theorem sum_of_prod {n : ℕ} (u v : Fin n → ℂ) (h : ∏ j, (X - C (u j)) = ∏ j, (X - C (v j))) :
    ∑ j, u j = ∑ j, v j := by
  have key : ∀ u : Fin n → ℂ, (∏ j, (X - C (u j)) : ℂ[X]).roots = Finset.univ.val.map u := fun u => by
    rw [Finset.prod_eq_multiset_prod]
    have := roots_multiset_prod_X_sub_C (Finset.univ.val.map u)
    rwa [Multiset.map_map] at this
  exact congrArg Multiset.sum (((key u).symm.trans (congrArg roots h)).trans (key v))
end UpperTheory.V.Z.J.D.TypeVAux

open UpperTheory.V.Z.J.D UpperTheory.V.Z.J.D.TypeVAux in
theorem UpperTheory.V.Z.J.D.type_v_statement :
    _root_.UpperTheory.V.Z.J.D.TypeVAlt := by
  intro P L Ω _ _ _ _ _ _ n hn π w A h τ hτ χ hχ rc hrc hT
  obtain ⟨a, ha, ε, H⟩ := hrc
  have hart : a = artOf h := by
    have ha' : IsLocalArtin h (artOf h) := Classical.epsilon_spec (p := IsLocalArtin h) ⟨a, ha⟩
    obtain ⟨art, hart⟩ := P.aut.art L Ω
    have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' L Ω art hart w
    exact MonoidHom.ext fun σ => hinj ((ha.glob art hart _).trans (ha'.glob art hart _).symm)
  obtain ⟨b, hb, hN, hI⟩ := hT
  choose ψ hψ using hχ
  have hcomm : ∀ s t, b.ρ s * b.ρ t = b.ρ t * b.ρ s := by
    intro s t
    have hd : deg (⁅s, t⁆ : Weil h) = 0 := by
      have h0 : degHom h ⁅s, t⁆ = 1 := by
        rw [map_commutatorElement]
        exact (Commute.all _ _).commutator_eq
      rwa [degHom_apply, ofAdd_eq_one] at h0
    let c : Ine (F := L) A := ⟨_, deg_eq_zero_iff.1 hd⟩
    have hcc : ineIncl h c = ⁅s, t⁆ := Subtype.ext rfl
    have h1 : b.ρ ⁅s, t⁆ = 1 := by
      have h2 : ∀ i, (χ i c : ℂ) = 1 := fun i => by
        rw [← hψ i c, hcc, map_commutatorElement, (Commute.all _ _).commutator_eq]
        rfl
      rw [← hcc, hI c]
      simp [h2]
      rfl
    have e : s * t = ⁅s, t⁆ * (t * s) := by
      rw [commutatorElement_def]
      group
    rw [← map_mul, ← map_mul, e, map_mul, h1, one_mul]
  obtain ⟨η, hcp, hone⟩ := exists_chars b.ρ b.semisimple hcomm
  have hsum : ∀ s : Ine (F := L) A, ∑ j, ((Units.coeHom ℂ).comp ((η j).comp (ineIncl h))) s =
      ∑ i, ((Units.coeHom ℂ).comp (χ i)) s := by
    intro s
    refine sum_of_prod _ _ ?_
    have h1 := hcp (ineIncl h s)
    rw [hI s, ← LinearMap.charpoly_toMatrix _ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin', Matrix.charpoly_diagonal] at h1
    exact h1.symm
  obtain ⟨e, he⟩ := exists_perm _ _ hsum
  have hηχ : ∀ i (g : Ine (F := L) A), η (e i) (ineIncl h g) = χ i g := fun i g =>
    Units.ext (DFunLike.congr_fun (he i) g)
  have hsm : ∀ j, GlobalTheory.WeilDeligne.IsSmooth (η j) := fun j => b.smooth.of_le fun σ hσ => hone j σ hσ
  choose ω hωs hωe using fun i => ha.factor (η (e i)) (hsm _)
  refine ⟨ω, hωs, ?_, fun i g => ?_⟩
  · refine _root_.UpperTheory.V.Z.J.D.TypeVAux.nonempty_equiv_principal_series_of_char_poly_of_generic P.loc H _ ω hωs (fun s => ?_) ⟨b, hb, hN⟩
      (GlobalTheory.ThK.DetProd.exists_isGeneric_of_isLocComp hτ)
    rw [← hb, WD.charPol_mk, hcp s, ← Equiv.prod_comp e]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hωe i]
    rfl
  · rw [← hart, ← hηχ i g, hωe i]
    rfl
end
end
end
end
