module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalJacquetSubquotientAtMostOneNonemptyBlock
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubquotientEigenvectorStatement
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalJacquetSubquotientAtMostOneNonemptyBlockStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.cuspidal_jacquet_subquotient_at_most_one_nonempty_block : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (s' : ℕ) (b : Fin s' → ℕ) (f : (Σ j, Fin (b j)) ≃ Fin d) (X : Fin s' → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (GL (Fin (b j)) k) (X j)), GlobalTheory.SmGL.IsCuspidal σ → (∀ j, Nontrivial (X j)) → GlobalTheory.SmGL.IsSubquotient (GlobalTheory.SmGL.piTensor ρ) (GlobalTheory.SmGL.jac f σ) → ∀ j j', 0 < b j → 0 < b j' → j = j' := by
  first | exact @GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal | exact GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal | (intros; apply GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleGl1IsoDet

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GLOneChar

open GlobalTheory.SmGL

theorem equiv_detRep_of_isIrreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (ω : kˣ →* ℂˣ), d = 1 → σ.IsIrreducible → GlobalTheory.SmGL.HasCentralChar σ ω → Nonempty (σ.Equiv (GlobalTheory.SmGL.detRep (Fin d) ω)) := by
  intro k _ _ _ _ d V _ _ σ ω hd hirr hω
  have hact : ∀ (g : GL (Fin d) k) (v : V), σ g v = (ω (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
    intro g v
    conv_lhs => rw [GlobalTheory.ProdSupport.eq_scalar_det hd g]
    exact hω _ v
  haveI : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have : (⊥ : Subrepresentation σ) = ⊤ :=
      Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
    exact bot_ne_top this
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S : Subrepresentation σ := ⟨ℂ ∙ v, fun g w hw => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [hact, smul_smul]
    exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩⟩
  have hS : S = ⊤ := by
    rcases eq_bot_or_eq_top S with h | h
    · exfalso
      have : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
      rw [h] at this
      exact hv this
    · exact h
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton ℂ V v) := by
    intro w
    have hw : w ∈ S.toSubmodule := by rw [hS]; trivial
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨c, rfl⟩
  have hinj : Function.Injective (LinearMap.toSpanSingleton ℂ V v) := by
    intro a b hab
    simp only [LinearMap.toSpanSingleton_apply] at hab
    exact smul_left_injective ℂ hv hab
  let e : ℂ ≃ₗ[ℂ] V := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  refine ⟨(Representation.Equiv.mk e fun g => ?_).symm⟩
  ext c
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, e,
    LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply, detRep, ofChar_apply,
    detChar_apply, hact, smul_smul, smul_eq_mul]
  rw [mul_one, ← LinearEquiv.map_smul, smul_eq_mul, mul_one]

end GlobalTheory.GLOneChar
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleGl1IsoDetStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.irreducible_gl1_iso_det : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (ω : kˣ →* ℂˣ), d = 1 → σ.IsIrreducible → GlobalTheory.SmGL.HasCentralChar σ ω → Nonempty (σ.Equiv (GlobalTheory.SmGL.detRep (Fin d) ω)) := by
  first | exact @GlobalTheory.GLOneChar.equiv_detRep_of_isIrreducible | exact GlobalTheory.GLOneChar.equiv_detRep_of_isIrreducible | (intros; apply GlobalTheory.GLOneChar.equiv_detRep_of_isIrreducible <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetRankOneCentral

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.JacGL1


open GlobalTheory.SmGL GlobalTheory.PRep Matrix in
theorem jac_mulSingle_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (ω : kˣ →* ℂˣ) (s' : ℕ) (b : Fin s' → ℕ) (f : (Σ j, Fin (b j)) ≃ Fin d) (j : Fin s'), d = 1 → b j = 1 → GlobalTheory.SmGL.HasCentralChar σ ω → ∀ (z : kˣ) (x : GlobalTheory.PRep.Jacquet σ (GlobalTheory.SmGL.unipRad k f)), GlobalTheory.SmGL.jac f σ (Pi.mulSingle j (Matrix.GeneralLinearGroup.scalar (Fin (b j)) z)) x = (ω z : ℂ) • x := by
  intro k _ _ _ _ d V _ _ σ ω s' b f j hd hj hω z x
  have hsum : ∑ i, b i = 1 := by
    have := Fintype.card_congr f
    simpa [Fintype.card_sigma, hd] using this
  have hsplit := Finset.add_sum_erase Finset.univ b (Finset.mem_univ j)
  have ha : ∀ i, i ≠ j → IsEmpty (Fin (b i)) := fun i hi => by
    have h0 : ∑ i ∈ Finset.univ.erase j, b i = 0 := by omega
    rw [Finset.sum_eq_zero_iff.1 h0 i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)]
    infer_instance
  have h1 : leviEmb k f (Pi.mulSingle j (GeneralLinearGroup.scalar (Fin (b j)) z)) =
      GeneralLinearGroup.scalar (Fin d) z := by
    ext i i'
    obtain ⟨⟨a, y⟩, rfl⟩ := f.surjective i
    obtain ⟨⟨a', y'⟩, rfl⟩ := f.surjective i'
    obtain rfl : a = j := by_contra fun h => (ha a h).elim y
    obtain rfl : a' = a := by_contra fun h => (ha a' h).elim y'
    rw [leviEmb_apply_same]
    simp [GeneralLinearGroup.scalar, diagonal_apply]
  have h2 : modExp (fun i => Fin (b i)) j = 0 := by
    unfold modExp
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
    · intro a hb
      have := ha a (Finset.mem_filter.1 hb).2.ne
      exact Nat.cast_eq_zero.2 Fintype.card_eq_zero
    · intro a hb
      have := ha a (Finset.mem_filter.1 hb).2.ne'
      exact Nat.cast_eq_zero.2 Fintype.card_eq_zero
  have h3 : deltaHalf k (fun i => Fin (b i))
      (Pi.mulSingle j (GeneralLinearGroup.scalar (Fin (b j)) z)) = 1 := by
    rw [deltaHalf_apply]
    refine Finset.prod_eq_one fun a _ => ?_
    by_cases hb : a = j
    · subst hb
      simp [h2]
    · rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one]
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine (jac_mk f σ _ v).trans ?_
  rw [h3, h1, hω z v, inv_one, Units.val_one, one_smul]
  exact map_smul (Submodule.mkQ _) _ _

end GlobalTheory.JacGL1
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetRankOneCentralStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.jacquet_rank_one_central : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (ω : kˣ →* ℂˣ) (s' : ℕ) (b : Fin s' → ℕ) (f : (Σ j, Fin (b j)) ≃ Fin d) (j : Fin s'), d = 1 → b j = 1 → GlobalTheory.SmGL.HasCentralChar σ ω → ∀ (z : kˣ) (x : GlobalTheory.PRep.Jacquet σ (GlobalTheory.SmGL.unipRad k f)), GlobalTheory.SmGL.jac f σ (Pi.mulSingle j (Matrix.GeneralLinearGroup.scalar (Fin (b j)) z)) x = (ω z : ℂ) • x := by
  first | exact @GlobalTheory.JacGL1.jac_mulSingle_scalar | exact GlobalTheory.JacGL1.jac_mulSingle_scalar | (intros; apply GlobalTheory.JacGL1.jac_mulSingle_scalar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardLeUnramifiedTwistsCuspidalSupportJacquet

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.JacSuppCount


open GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel in
theorem eq_mul_unrChar_of_eq_on_units : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ ω : kˣ →* ℂˣ), (∀ u : kˣ, ValuativeRel.valuation k (u : k) = 1 → ω u = χ u) → ∃ α : ℂˣ, ω = χ * GlobalTheory.SmGL.unrChar k α := by
  intro k _ _ _ _ χ ω h
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
    obtain ⟨x, hx⟩ := valuation_surjective (K := k) (uniformizer k)
    have h0 : x ≠ 0 := by
      rintro rfl
      exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)
    exact ⟨Units.mk0 x h0, hx⟩
  have hu : IsUnram (χ⁻¹ * ω) := fun u hu => by
    simp [h u hu]
  refine ⟨(χ⁻¹ * ω) ϖ, ?_⟩
  rw [← eq_unrChar hu hϖ]
  ext u
  simp


open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.ProdSupport Matrix ValuativeRel TensorProduct in
theorem scalar_mem_KO_of_val {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : Type) [Fintype m] [DecidableEq m] {z : kˣ} (hz : ValuativeRel.valuation k (z : k) = 1) :
    GeneralLinearGroup.scalar m z ∈ KO k m := by
  have hz' : ValuativeRel.valuation k ((z⁻¹ : kˣ) : k) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hz, inv_one]
  have h1 : (z : k) ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hz.le
  have h2 : ((z⁻¹ : kˣ) : k) ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hz'.le
  refine (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · by_cases h : i = j
    · subst h; simpa [GeneralLinearGroup.scalar] using h1
    · simp [GeneralLinearGroup.scalar, h, zero_mem]
  · rw [← map_inv]
    by_cases h : i = j
    · subst h; simpa [GeneralLinearGroup.scalar] using h2
    · simp [GeneralLinearGroup.scalar, h, zero_mem]


open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.ProdSupport Matrix ValuativeRel TensorProduct in
theorem card_le_ncard_unrTwist : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s s' : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k n) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (d' : Fin s' → ℕ) (e : (Σ j, Fin (d' j)) ≃ Fin n) (A : Finset (Fin s')) (x : GlobalTheory.PRep.Jacquet π.π (GlobalTheory.SmGL.unipRad k e)), GlobalTheory.SmGL.IsSmoothChar χ → GlobalTheory.SmGL.IsCuspSupport π.π d (fun a => (σ a).π) → (∀ j ∈ A, d' j = 1) → x ≠ 0 → (∀ j ∈ A, ∀ g ∈ GlobalTheory.SplitWeil.KO k (Fin (d' j)), GlobalTheory.SmGL.jac e π.π (Pi.mulSingle j g) x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x) → A.card ≤ Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (GlobalTheory.SmGL.detRep (Fin (d a)) (χ * GlobalTheory.SmGL.unrChar k α)))} := by
  intro _ hG k _ _ _ _ n s s' χ π d σ d' e A x hχ hcs hA hx hact
  obtain ⟨-, hσ, e₀, hsub⟩ := hcs
  obtain ⟨Y, _, _, τ, y, hτ, hτs, hy, hτy⟩ := GlobalTheory.T.irreducible_subquotient_eigenvector _ _ (jac e π.π) x hx
  have hτP : IsSubquotient τ (jac e (multiProd e₀ fun a => (σ a).π)) :=
    hτs.trans (GlobalTheory.JacquetExact.isSubquotient_jac e (isSmooth_parInd _ _) hsub)
  obtain ⟨b, f, g, t, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2 e₀ e
    (fun a => (σ a).smooth) (fun a => hasFiniteLength_of_isIrreducible (σ a).irr) hτ hτP

  have hcolj : ∀ j ∈ A, ∃ i, b.1 i j = 1 ∧ ∀ i', i' ≠ i → b.1 i' j = 0 := by
    intro j hj
    have hsum : ∑ i, b.1 i j = 1 := by simpa [hA j hj] using b.2.2 j
    obtain ⟨i, -, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.trans_ne one_ne_zero)
    have hsplit := Finset.add_sum_erase Finset.univ (fun i => b.1 i j) (Finset.mem_univ i)
    have h0 : ∑ i' ∈ Finset.univ.erase i, b.1 i' j = 0 := by simp only at hsplit; omega
    refine ⟨i, by simp only at hsplit; omega, fun i' hi' => ?_⟩
    exact Finset.sum_eq_zero_iff.1 h0 i' (Finset.mem_erase.2 ⟨hi', Finset.mem_univ i'⟩)
  rcases A.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
  · simp
  haveI : Nonempty (Fin s) := ⟨(hcolj j₀ hj₀).choose⟩
  choose! ι hι1 hι0 using hcolj

  have hrow1 : ∀ i j j', 0 < b.1 i j → 0 < b.1 i j' → j = j' := fun i =>
    GlobalTheory.T.cuspidal_jacquet_subquotient_at_most_one_nonempty_block k (d i) _ (σ i).π s' (b.1 i) (f i) _ (fun j => (t i j).ρ) (hσ i).2.2
      (fun j => Model.nontrivial_of_isIrreducible (t i j).irr) (hrow i)

  have hd1 : ∀ j ∈ A, d (ι j) = 1 := by
    intro j hj
    have h := b.2.1 (ι j)
    rw [Fintype.card_fin, Finset.sum_eq_single j (fun j' _ hj' => by
      by_contra hne
      exact hj' (hrow1 _ _ _ (Nat.pos_of_ne_zero hne) (by rw [hι1 j hj]; exact one_pos)))
      (by simp), hι1 j hj] at h
    exact h.symm
  have hinj : Set.InjOn ι (A : Set (Fin s')) := by
    intro j hj j' hj' h
    refine hrow1 (ι j) j j' (by rw [hι1 j hj]; exact one_pos) ?_
    rw [h, hι1 j' hj']; exact one_pos

  have hmem : ∀ j ∈ A, ι j ∈ {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv
      (GlobalTheory.SmGL.detRep (Fin (d a)) (χ * GlobalTheory.SmGL.unrChar k α)))} := by
    intro j hj
    set i := ι j with hi
    obtain ⟨ω, -, hω⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar (σ i).smooth (σ i).irr

    have hT : ∀ (z : kˣ) (v : ⨂[ℂ] j', (t i j').V),
        piTensor (fun j' => (t i j').ρ) (Pi.mulSingle j (GeneralLinearGroup.scalar (Fin (b.1 i j)) z)) v =
          (ω z : ℂ) • v := fun z v =>
      Model.scalar_of_isSubquotient (hrow i) (GlobalTheory.T.jacquet_rank_one_central k (d i) _ (σ i).π ω s' (b.1 i) (f i) j (hd1 j hj)
        (hι1 j hj) hω z) v
    have hωt : HasCentralChar (t i j).ρ ω := by
      obtain ⟨ω', -, hω'⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar (t i j).smooth (t i j).irr
      have := nontrivial_piTensor _ fun j' => Model.nontrivial_of_isIrreducible (t i j').irr
      obtain ⟨v, hv⟩ := exists_ne (0 : ⨂[ℂ] j', (t i j').V)
      have : ω' = ω := MonoidHom.ext fun z => Units.ext (smul_left_injective ℂ hv
        ((piTensor_mulSingle (fun j' => (t i j').ρ) j _ _ (hω' z) v).symm.trans (hT z v)))
      exact this ▸ hω'
    have hz : ∀ i', i' ≠ i → IsEmpty (Fin (b.1 i' j)) := fun i' h' => by
      rw [hι0 j hj i' h']; infer_instance
    have hcen := hasCentralChar_multiProd (g j) (fun i' => (t i' j).ρ) i hz hωt
    have hωχ : ∀ u : kˣ, ValuativeRel.valuation k (u : k) = 1 → ω u = χ u := by
      intro u hu
      have h1 := Model.scalar_of_isSubquotient hcol
        (piTensor_mulSingle (fun j => multiProd (g j) fun i => (t i j).ρ) j _ _ (hcen u)) y
      have h2 := hτy _ _ (hact j hj _ (scalar_mem_KO_of_val (Fin (d' j)) hu))
      rw [det_scalar_one (hA j hj)] at h2
      exact Units.ext (smul_left_injective ℂ hy (h1.symm.trans h2))
    obtain ⟨α, hα⟩ := eq_mul_unrChar_of_eq_on_units k χ ω hωχ
    exact ⟨hd1 j hj, α, hα ▸ GlobalTheory.T.irreducible_gl1_iso_det k (d i) _ (σ i).π ω (hd1 j hj) (σ i).irr hω⟩
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard_of_injOn ι hmem hinj (Set.toFinite _)

end GlobalTheory.JacSuppCount
end
end
end
